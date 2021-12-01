import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Executor {
  type TaskChoice = BigInt
  type Schedule = List[TaskChoice]

  case class State[SharedState, TaskState](
      val shared: SharedState,
      val tasks: List[TaskState]
  ) {
    def taskNum = tasks.length
  }

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
      state: State[S, T],
      f: (S, T) => (S, T),
      choice: TaskChoice
  ): State[S, T] = {
    require(choiceValid(choice, state))

    val tasks = state.tasks
    val res = f(state.shared, tasks(choice))
    updatedListSameLength(tasks, choice, res._2)
    State[S, T](res._1, tasks.updated(choice, res._2))
  }.ensuring(res => res.taskNum == state.taskNum)

  def run[S, T](
      state: State[S, T],
      f: (S, T) => (S, T),
      schedule: Schedule
  ): State[S, T] = {
    require(scheduleValid(schedule, state))

    schedule match {
      case Nil() => state
      case Cons(choice, rest) => {
        val newState = runOne(state, f, choice)

        scheduleValidStateContentAgnostic(rest, state, newState)
        run(newState, f, rest)
      }
    }
  }

  def updatedListSameLength[T](l: List[T], i: BigInt, elem: T): Unit = {
    require(i >= 0 && i < l.length)
    if (i == 0) {
      assert(l.updated(i, elem).tail == l.tail)
    } else {
      updatedListSameLength(l.tail, i - 1, elem)
    }
  }.ensuring(l.updated(i, elem).length == l.length)
}
