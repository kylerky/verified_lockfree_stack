package concurrent

import stainless.lang._
import stainless.collection._
import stainless.annotation._

import runtime.Executor
import runtime.Executor.{State, Schedule, History, TaskChoice}

object TreiberStack {
  sealed abstract class TaskState[T]
  case class PushRead[T](v: T) extends TaskState[T]
  case class PushTry[T](v: T, oldHead: Option[Node[T]]) extends TaskState[T]
  case class PopRead[T]() extends TaskState[T]
  case class PopTry[T](oldHead: Option[Node[T]]) extends TaskState[T]

  sealed abstract class Result[T]
  case class PopSuccessNone[T]() extends Result[T]
  case class PopSuccessSome[T](v: T) extends Result[T]
  case class PushSuccess[T]() extends Result[T]
  case class Pending[T]() extends Result[T]

  case class Node[T](value: T, next: Option[Node[T]])

  case class Shared[T](
      head: Option[Node[T]],
      @ghost
      reference: List[T],
      res: Result[T]
  )

  type StackState[T] = State[Shared[T], TaskState[T]]

  def nop[T](x: Shared[T], y: TaskState[T]) = { (x, y) }
    .ensuring(res => res._1 == x && res._2 == y)

  def nopTaskStateEqual[T](
      oldState: StackState[T],
      newState: StackState[T],
      choice: TaskChoice
  ): Unit = {
    require(choice >= 0)

    val oldTasks = oldState.tasks
    val newTasks = newState.tasks
    require(oldTasks.length > choice)
    require(newTasks.length > choice)
    require(
      newTasks == oldTasks.updated(
        choice,
        nop(oldState.shared, oldTasks(choice))._2
      )
    )

    if (choice != 0) {
      nopTaskStateEqual(
        oldState.copy(tasks = oldState.tasks.tail),
        newState.copy(tasks = newState.tasks.tail),
        choice - 1
      )
    }
  }.ensuring(oldState.tasks == newState.tasks)

  def runNop[T](schedule: Schedule, s: StackState[T]): List[StackState[T]] = {
    require(Executor.scheduleValid(schedule, s))

    def pred(s0: StackState[T]) = { s0 == s }

    val res = Executor
      .runMaintainsInvariant(pred, nop[T], s, schedule)

    def nopDoesNothing(
        history: History[Shared[T], TaskState[T]],
        schedule: Schedule
    ): Unit = {
      decreases(history.length)

      require(history.nonEmpty)
      require(
        Executor.runConsistent(nop[T], schedule, history)
      )
      assert(history.length == schedule.length + 1)

      schedule match {
        case Nil() =>
        case Cons(choice, rest) => {

          assert(Executor.choiceValid(choice, history.head))
          val state = history.head
          val newState = Executor.runOne(nop[T], state, choice)
          assert(newState.shared == state.shared)

          nopTaskStateEqual(state, newState, choice)
          assert(newState == state)

          assert(pred(state) ==> pred(Executor.runOne(nop[T], state, choice)))

          Executor.runConsistentSubHistory(nop[T], schedule, history)
          nopDoesNothing(history.tail, schedule.tail)
        }
      }
    }.ensuring(
      Executor.historyMaintainsInvariant(pred, nop[T], history, schedule)
    )

    nopDoesNothing(res, schedule)
    Executor.predicateForAllPremiseTrue(pred, nop[T], s, res, schedule)
    assert(Executor.predicateForAll(pred, res))

    res
  }

  def stackStateValid[T](s: StackState[T]): Boolean = {
    stackSharedStateValid(s.shared)
  }

  def stackSharedStateValid[T](shared: Shared[T]): Boolean = {
    shared match {
      case Shared(None(), Nil(), _) => true
      case Shared(Some(v), Cons(head, rest), _) =>
        (v.value == head) && stackSharedStateValid(
          shared.copy(head = v.next, reference = rest)
        )
      case Shared(_, _, _) => false
    }
  }

  def stackSharedStateValidResAgnorant[T](
      shared: Shared[T],
      r: Result[T]
  ): Unit = {
    shared match {
      case Shared(None(), Nil(), _) =>
      case Shared(Some(v), Cons(head, rest), _) =>
        stackSharedStateValidResAgnorant(
          shared.copy(head = v.next, reference = rest),
          r
        )
      case Shared(_, _, _) =>
    }
  }.ensuring(
    stackSharedStateValid(shared) ==> stackSharedStateValid(
      shared.copy(res = r)
    )
  )

  def popResMatch[T](shared: Shared[T], newShared: Shared[T]): Boolean = {
    (shared, newShared.res) match {
      case (Shared(_, _, _), Pending()) => true
      case (Shared(_, Cons(head, _), _), PopSuccessSome(r)) => {
        r == head
      }
      case (Shared(_, Nil(), _), PopSuccessNone()) => true
      case _                                       => false
    }
  }

  @ghost
  def referenceWorkAround[T](reference: List[T], v: T) =
    if (reference.isEmpty) List(v) else reference

  def stackOp[T](x: Shared[T], y: TaskState[T]): (Shared[T], TaskState[T]) = {
    y match {
      case PushRead(v) => {
        stackSharedStateValidResAgnorant(x, Pending())
        (x.copy(res = Pending()), PushTry(v, x.head))
      }

      case PushTry(v, oldHead) if x.head == oldHead => {
        val node = Node(v, oldHead)
        stackSharedStateValidResAgnorant(
          Shared(Some(node), Cons(v, x.reference), x.res),
          PushSuccess()
        )
        (Shared(Some(node), Cons(v, x.reference), PushSuccess()), PushRead(v))
      }

      case PushTry(v, oldHead) => {
        stackSharedStateValidResAgnorant(x, Pending())
        (x.copy(res = Pending()), PushRead(v))
      }

      case PopRead() => {
        stackSharedStateValidResAgnorant(x, Pending())
        (x.copy(res = Pending()), PopTry(x.head))
      }

      case PopTry(None()) if x.head.isEmpty => {
        stackSharedStateValidResAgnorant(x, PopSuccessNone())
        (x.copy(res = PopSuccessNone()), PopRead[T]())
      }

      case PopTry(Some(v)) if x.head == Some(v) => {
        val newHead = v.next
        // work around in case `reference` is empty
        @ghost
        val reference = referenceWorkAround(x.reference, v.value)
        stackSharedStateValidResAgnorant(
          Shared(newHead, reference.tail, x.res),
          PopSuccessSome(v.value)
        )
        (
          Shared(newHead, reference.tail, PopSuccessSome(v.value)),
          PopRead[T]()
        )
      }

      case PopTry(_) => {
        stackSharedStateValidResAgnorant(x, Pending())
        (x.copy(res = Pending()), PopRead[T]())
      }
    }
  }.ensuring(res =>
    (stackSharedStateValid(x) ==> (stackSharedStateValid(res._1)
      && (y.isInstanceOf[PopTry[T]] ==> popResMatch(x, res._1))))
      && (!y.isInstanceOf[PopTry[T]] ==>
        (!res._1.res.isInstanceOf[PopSuccessNone[T]]
          && !res._1.res.isInstanceOf[PopSuccessSome[T]]))
  )

  def run[T](schedule: Schedule, s: StackState[T]): List[StackState[T]] = {
    require(Executor.scheduleValid(schedule, s))
    require(stackStateValid(s))

    val res = Executor
      .runMaintainsInvariant(stackStateValid[T], stackOp[T], s, schedule)

    def opMaintainsInvariant(
        history: History[Shared[T], TaskState[T]],
        schedule: Schedule
    ): Unit = {
      decreases(history.length)

      require(history.nonEmpty)
      require(
        Executor.runConsistent(stackOp[T], schedule, history)
      )
      assert(history.length == schedule.length + 1)

      schedule match {
        case Nil() =>
        case Cons(choice, rest) => {
          assert(Executor.choiceValid(choice, history.head))
          val state = history.head
          val newState = Executor.runOne(stackOp[T], state, choice)

          assert(stackStateValid(state) ==> stackStateValid(newState))

          assert(
            stackStateValid(state) ==> stackStateValid(
              Executor.runOne(stackOp[T], state, choice)
            )
          )

          Executor.runConsistentSubHistory(stackOp[T], schedule, history)
          opMaintainsInvariant(history.tail, schedule.tail)
        }
      }
    }.ensuring(
      Executor.historyMaintainsInvariant(
        stackStateValid[T],
        stackOp[T],
        history,
        schedule
      )
    )

    opMaintainsInvariant(res, schedule)
    Executor.predicateForAllPremiseTrue(
      stackStateValid[T],
      stackOp[T],
      s,
      res,
      schedule
    )
    assert(Executor.predicateForAll(stackStateValid[T], res))

    res
  }

  def findSuccessfulOperation[T](
      history: History[Shared[T], TaskState[T]],
      schedule: Schedule,
      start: BigInt
  ): Option[BigInt] = {
    require(history.nonEmpty)
    require(schedule.length >= 1)
    require(schedule.length >= start)
    require(
      Executor.runConsistent(stackOp[T], schedule, history)
    )
    require(start >= 0)
    assert(history.length >= start + 1)

    Executor.runConsistentSubHistory(stackOp[T], schedule, history, start)

    val subHistory = history.drop(start)
    findSuccessfulOperationIndex(
      subHistory,
      schedule.drop(start),
      0,
      subHistory,
      0
    )
  }.ensuring(
    true
    // _.map(i =>
    //   i + start + 1 >= 0
    //     && i + start + 1 < history.length
    //     && !history(i + start + 1).shared.res
    //       .isInstanceOf[Pending[T]]
    // )
    //   .getOrElse(true)
  )

  def canSucceed[T](shared: Shared[T], taskState: TaskState[T]): Boolean = {
    taskState match {
      case PushTry(v, oldHead) if oldHead == shared.head => true
      case PopTry(oldHead) if oldHead == shared.head     => true
      case _                                             => false
    }
  }

  def canSucceedWillSucceed[T](
      choice: TaskChoice,
      sOld: StackState[T],
      sNew: StackState[T]
  ) = {
    require(Executor.choiceValid(choice, sOld))
    require(sNew == Executor.runOne(stackOp[T], sOld, choice))
    require(canSucceed(sOld.shared, sOld.tasks(choice)))
  }.ensuring(!sNew.shared.res.isInstanceOf[Pending[T]])

  def numCandidate[T](state: StackState[T]): BigInt = {
    numCandidate(state.shared, state.tasks)
  }

  def numCandidate[T](shared: Shared[T], tasks: List[TaskState[T]]): BigInt = {
    tasks.count(state => canSucceed(shared, state))
  }

  def numFailedAttempts[T](s: StackState[T]): BigInt = {
    numFailedAttempts(s.shared, s.tasks)
  }

  def numFailedAttempts[T](
      shared: Shared[T],
      tasks: List[TaskState[T]]
  ): BigInt = {
    tasks.count(state =>
      !canSucceed(shared, state) &&
        (state.isInstanceOf[PopTry[T]] || state.isInstanceOf[PushTry[T]])
    )
  }

  def numCandidateEqual[T](s0: StackState[T], s1: StackState[T]): Unit = {
    require(s0.shared.head == s1.shared.head)
    require(s0.tasks == s1.tasks)
    if (s0.tasks.nonEmpty) {
      numCandidateEqual(
        s0.copy(tasks = s0.tasks.tail),
        s1.copy(tasks = s1.tasks.tail)
      )
    }
  }.ensuring(numCandidate(s0) == numCandidate(s1))

  def numCandidateNotDecreasing[T](
      choice: TaskChoice,
      sOld: StackState[T],
      sNew: StackState[T]
  ): Unit = {
    require(Executor.choiceValid(choice, sOld))
    require(sNew == Executor.runOne(stackOp[T], sOld, choice))
    require(!canSucceed(sOld.shared, sOld.tasks(choice)))
    if (choice == 0) {
      val newTail = sNew.copy(tasks = sNew.tasks.tail)
      val oldTail = sOld.copy(tasks = sOld.tasks.tail)
      numCandidateEqual(newTail, oldTail)
    } else {
      numCandidateNotDecreasing(
        choice - 1,
        sOld.copy(tasks = sOld.tasks.tail),
        sNew.copy(tasks = sNew.tasks.tail)
      )
    }
  }.ensuring(numCandidate(sNew) >= numCandidate(sOld))

  def numCandidateIncreasing[T](
      choice: TaskChoice,
      sOld: StackState[T],
      sNew: StackState[T]
  ): Unit = {
    require(Executor.choiceValid(choice, sOld))
    require(sNew == Executor.runOne(stackOp[T], sOld, choice))
    require(
      sOld.tasks(choice).isInstanceOf[PushRead[T]] ||
        sOld.tasks(choice).isInstanceOf[PopRead[T]]
    )

    if (choice == 0) {
      val newTail = sNew.copy(tasks = sNew.tasks.tail)
      val oldTail = sOld.copy(tasks = sOld.tasks.tail)
      numCandidateEqual(newTail, oldTail)
    } else {
      numCandidateIncreasing(
        choice - 1,
        sOld.copy(tasks = sOld.tasks.tail),
        sNew.copy(tasks = sNew.tasks.tail)
      )
    }
  }.ensuring(numCandidate(sNew) >= (numCandidate(sOld) + 1))

  def numFailedAttemptsEqual[T](s0: StackState[T], s1: StackState[T]): Unit = {
    require(s0.shared.head == s1.shared.head)
    require(s0.tasks == s1.tasks)
    if (s0.tasks.nonEmpty) {
      numFailedAttemptsEqual(
        s0.copy(tasks = s0.tasks.tail),
        s1.copy(tasks = s1.tasks.tail)
      )
    }
  }.ensuring(numFailedAttempts(s0) == numFailedAttempts(s1))

  def numFailedAttemptsDecreasing[T](
      choice: TaskChoice,
      sOld: StackState[T],
      sNew: StackState[T]
  ): Unit = {
    require(Executor.choiceValid(choice, sOld))
    require(sNew == Executor.runOne(stackOp[T], sOld, choice))
    require(
      !sOld.tasks(choice).isInstanceOf[PushRead[T]] &&
        !sOld.tasks(choice).isInstanceOf[PopRead[T]]
    )
    require(!canSucceed(sOld.shared, sOld.tasks(choice)))

    if (choice == 0) {
      val newTail = sNew.copy(tasks = sNew.tasks.tail)
      val oldTail = sOld.copy(tasks = sOld.tasks.tail)
      numFailedAttemptsEqual(newTail, oldTail)
    } else {
      numFailedAttemptsDecreasing(
        choice - 1,
        sOld.copy(tasks = sOld.tasks.tail),
        sNew.copy(tasks = sNew.tasks.tail)
      )
    }
  }.ensuring(numFailedAttempts(sNew) <= (numFailedAttempts(sOld) - 1))

  def numFailedAttemptsNotIncreasing[T](
      choice: TaskChoice,
      sOld: StackState[T],
      sNew: StackState[T]
  ): Unit = {
    require(Executor.choiceValid(choice, sOld))
    require(sNew == Executor.runOne(stackOp[T], sOld, choice))
    require(
      sOld.tasks(choice).isInstanceOf[PushRead[T]] ||
        sOld.tasks(choice).isInstanceOf[PopRead[T]]
    )
    require(!canSucceed(sOld.shared, sOld.tasks(choice)))

    if (choice == 0) {
      val newTail = sNew.copy(tasks = sNew.tasks.tail)
      val oldTail = sOld.copy(tasks = sOld.tasks.tail)
      numFailedAttemptsEqual(newTail, oldTail)
    } else {
      numFailedAttemptsNotIncreasing(
        choice - 1,
        sOld.copy(tasks = sOld.tasks.tail),
        sNew.copy(tasks = sNew.tasks.tail)
      )
    }
  }.ensuring(numFailedAttempts(sNew) <= (numFailedAttempts(sOld)))

  def listDropSublist[T](l: List[T], i: BigInt): Unit = {
    require(i >= 0)
    require(i + 1 < l.length)
    if (i != 0) {
      listDropSublist(l.tail, i - 1)
    }
  }.ensuring(l.drop(i + 1) == l.drop(i).tail)

  def listDropApply[T](l: List[T], i: BigInt, j: BigInt): Unit = {
    require(i >= 0)
    require(j >= 0)
    require(i + j < l.length)
    if (i != 0) {
      listDropApply(l.tail, i - 1, j)
    }
  }.ensuring(l.drop(i)(j) == l(i + j))

  def findSuccessfulOperationIndex[T](
      history: History[Shared[T], TaskState[T]],
      schedule: Schedule,
      i: BigInt,
      fullHistory: History[Shared[T], TaskState[T]],
      numRetries: BigInt
  ): Option[BigInt] = {
    require(history.nonEmpty)
    require(
      Executor.runConsistent(stackOp[T], schedule, history)
    )
    require(i < fullHistory.length)
    require(i >= 0)
    require(numRetries >= 0)
    require(fullHistory.drop(i) == history)
    require((i - numRetries) <= numCandidate(history.head))
    require(
      numFailedAttempts(
        history.head.shared,
        history.head.tasks
      ) + numRetries <= history.head.taskNum
    )

    decreases(history.length)

    if (schedule.isEmpty) {
      assert(fullHistory.length == i + 1)

      assert((i - numRetries) <= history.head.taskNum)
      assert(numRetries <= history.head.taskNum)
      assert(i <= 2 * history.head.taskNum)

      assert(fullHistory.length <= 2 * history.head.taskNum + 1)
      return None();
    }

    if (canSucceed(history.head.shared, history.head.tasks(schedule.head))) {
      canSucceedWillSucceed(schedule.head, history.head, history(1))
      assert(!history(1).shared.res.isInstanceOf[Pending[T]])

      assert((i - numRetries) <= history.head.taskNum)
      assert(numRetries <= history.head.taskNum)
      assert(i <= 2 * history.head.taskNum)

      listDropApply(fullHistory, i, 1)
      assert(fullHistory(i + 1) == history(1))

      return Some(i);
    }

    Executor.runConsistentSubHistory(stackOp[T], schedule, history)
    val currentState = history.head
    val choice = schedule.head
    if (
      currentState.tasks(choice).isInstanceOf[PushRead[T]] ||
      currentState.tasks(choice).isInstanceOf[PopRead[T]]
    ) {
      numCandidateIncreasing(choice, history.head, history.tail.head)
      numFailedAttemptsNotIncreasing(
        schedule.head,
        history.head,
        history.tail.head
      )

      listDropSublist(fullHistory, i)
      findSuccessfulOperationIndex(
        history.tail,
        schedule.tail,
        i + 1,
        fullHistory,
        numRetries
      )
    } else {
      numCandidateNotDecreasing(schedule.head, history.head, history.tail.head)
      numFailedAttemptsDecreasing(
        schedule.head,
        history.head,
        history.tail.head
      )

      listDropSublist(fullHistory, i)
      findSuccessfulOperationIndex(
        history.tail,
        schedule.tail,
        i + 1,
        fullHistory,
        numRetries + 1
      )
    }
  }.ensuring(res =>
    (fullHistory.length > 2 * history.head.taskNum + 1 ==> res.nonEmpty)
      && res
        .map(r =>
          r < fullHistory.length - 1
            && r >= 0
            && !fullHistory(r + 1).shared.res.isInstanceOf[Pending[T]]
        )
        .getOrElse(true)
  )
}
