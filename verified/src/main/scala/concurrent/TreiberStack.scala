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
  case class PopSuccess[T](v: T) extends Result[T]
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
      case (Shared(_, Cons(head, _), _), PopSuccess(r)) => {
        r == head
      }
      case _ => false
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
      case PushTry(v, oldHead) => {
        if (x.head == oldHead) {
          val node = Node(v, oldHead)
          stackSharedStateValidResAgnorant(
            Shared(Some(node), Cons(v, x.reference), x.res),
            PushSuccess()
          )
          (Shared(Some(node), Cons(v, x.reference), PushSuccess()), PushRead(v))
        } else {
          stackSharedStateValidResAgnorant(x, Pending())
          (x.copy(res = Pending()), PushRead(v))
        }
      }

      case PopRead() => {
        stackSharedStateValidResAgnorant(x, Pending())
        (x.copy(res = Pending()), PopTry(x.head))
      }
      case PopTry(oldHead) => {
        oldHead match {
          case None() => {
            stackSharedStateValidResAgnorant(x, Pending())
            (x.copy(res = Pending()), PopRead[T]())
          }
          case Some(v) => {
            val newHead = v.next
            if (x.head == oldHead) {
              // work around in case `reference` is empty
              @ghost
              val reference = referenceWorkAround(x.reference, v.value)
              stackSharedStateValidResAgnorant(
                Shared(newHead, reference.tail, x.res),
                PopSuccess(v.value)
              )
              (
                Shared(newHead, reference.tail, PopSuccess(v.value)),
                PopRead[T]()
              )
            } else {
              stackSharedStateValidResAgnorant(x, Pending())
              (x.copy(res = Pending()), PopRead[T]())
            }
          }
        }
      }
    }
  }.ensuring(res =>
    (stackSharedStateValid(x) ==> (stackSharedStateValid(res._1)
      && (y.isInstanceOf[PopTry[T]] ==> popResMatch(x, res._1))))
      && (!y.isInstanceOf[PopTry[T]] ==> !res._1.res
        .isInstanceOf[PopSuccess[T]])
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
}
