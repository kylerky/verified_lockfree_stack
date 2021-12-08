package runtime

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.equations._

object Executor {
  type TaskChoice = BigInt
  type Schedule = List[TaskChoice]

  case class State[SharedState, TaskState](
      val shared: SharedState,
      val tasks: List[TaskState]
  ) {
    def taskNum = tasks.length
  }

  type History[S, T] = List[State[S, T]];

  def choiceValid[S, T](choice: TaskChoice, state: State[S, T]): Boolean = {
    choice >= 0 && choice < state.tasks.length
  }

  def choiceValidContentAgnostic[S, T](
      choice: TaskChoice,
      s0: State[S, T],
      s1: State[S, T]
  ) = {
    require(s0.taskNum == s1.taskNum && choiceValid(choice, s0))
  }.ensuring(choiceValid(choice, s1))

  def scheduleValid[S, T](schedule: Schedule, state: State[S, T]): Boolean = {
    schedule.forall(choiceValid(_, state))
  }

  def scheduleValidStateContentAgnostic[S, T](
      @induct schedule: Schedule,
      s0: State[S, T],
      s1: State[S, T]
  ): Unit = {
    require(s0.taskNum == s1.taskNum && scheduleValid(schedule, s0))
  }.ensuring(scheduleValid(schedule, s1))

  def runOne[S, T](
      f: (S, T) => (S, T),
      state: State[S, T],
      choice: TaskChoice
  ): State[S, T] = {
    require(choiceValid(choice, state))

    val tasks = state.tasks
    val res = f(state.shared, tasks(choice))
    updatedListSameLength(tasks, choice, res._2)
    State[S, T](res._1, tasks.updated(choice, res._2))
  }.ensuring(res => res.taskNum == state.taskNum)

  def maintainInvariant[S, T](
      predicate: State[S, T] => Boolean,
      f: (S, T) => (S, T),
      state: State[S, T],
      choice: TaskChoice
  ): Boolean = {
    require(choiceValid(choice, state))
    val tasks = state.tasks
    val res = f(state.shared, tasks(choice))
    val newState = State[S, T](res._1, tasks.updated(choice, res._2))
    predicate(state) ==> predicate(newState)
  }

  def runOneMaintainsInvariant[S, T](
      predicate: State[S, T] => Boolean,
      f: (S, T) => (S, T),
      state: State[S, T],
      choice: TaskChoice
  ) = {
    require(choiceValid(choice, state))
    require(maintainInvariant(predicate, f, state, choice))
  }.ensuring(predicate(state) ==> predicate(runOne(f, state, choice)))

  def run[S, T](
      f: (S, T) => (S, T),
      state: State[S, T],
      schedule: Schedule
  ): History[S, T] = {
    require(scheduleValid(schedule, state))

    schedule match {
      case Nil() => List(state)
      case Cons(choice, rest) => {
        val newState = runOne(f, state, choice)

        scheduleValidStateContentAgnostic(rest, state, newState)
        state :: run(f, newState, rest)
      }
    }
  }

  def historyMaintainsInvariant[S, T](
      predicate: State[S, T] => Boolean,
      f: (S, T) => (S, T),
      history: History[S, T],
      schedule: Schedule
  ): Boolean = {
    require(history.nonEmpty)

    history.zip(schedule).forall { case (s, c) =>
      choiceValid(c, s) && maintainInvariant(predicate, f, s, c)
    }
  }

  def runMaintainsInvariant[S, T](
      predicate: State[S, T] => Boolean,
      f: (S, T) => (S, T),
      state: State[S, T],
      schedule: Schedule
  ): History[S, T] = {
    require(scheduleValid(schedule, state))

    val runHistory = run(f, state, schedule)

    val res = schedule match {
      case Nil() => List(state)
      case Cons(choice, rest) => {
        val newState = runOne(f, state, choice)
        state :: runMaintainsInvariant(predicate, f, newState, rest)
      }
    }

    assert(res == runHistory)
    runHistory
  }.ensuring(res =>
    (predicate(state) &&
      historyMaintainsInvariant(predicate, f, res, schedule)) ==>
      res.forall(predicate(_))
  )

  // auxiliary lemmas
  def updatedListSameLength[T](l: List[T], i: BigInt, elem: T): Unit = {
    require(i >= 0 && i < l.length)
    if (i == 0) {
      assert(l.updated(i, elem).tail == l.tail)
    } else {
      updatedListSameLength(l.tail, i - 1, elem)
    }
  }.ensuring(l.updated(i, elem).length == l.length)
}
