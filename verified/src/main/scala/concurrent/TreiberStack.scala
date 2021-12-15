package concurrent

import stainless.lang._
import stainless.collection._

import runtime.Executor
import runtime.Executor.{State, Schedule, History, TaskChoice}

object TreiberStack {
  type Shared = Int
  type TaskState = Int
  type StackState = State[Shared, TaskState]

  def nop(x: Int, y: Int) = { (x, y) }.ensuring(res =>
    res._1 == x && res._2 == y
  )

  // val initState: State[Int, Int] = State(0, List(0, 0))

  def nopTaskStateEqual(
      oldState: StackState,
      newState: StackState,
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

  def run(schedule: Schedule, s: StackState): List[StackState] = {
    require(Executor.scheduleValid(schedule, s))

    val pred = (s0: StackState) => s0 == s

    val res = Executor
      .runMaintainsInvariant(pred, nop, s, schedule)

    def nopDoesNothing(
        history: History[Shared, TaskState],
        schedule: Schedule
    ): Unit = {
      require(history.nonEmpty)
      require(Executor.runConsistent(nop, schedule, history))

      schedule match {
        case Nil() =>
        case Cons(choice, rest) => {
          assert(Executor.choiceValid(choice, history.head))
          val state = history.head
          val newState = Executor.runOne(nop, state, choice)
          assert(newState.shared == state.shared)

          nopTaskStateEqual(state, newState, choice)
          assert(newState == state)

          assert(pred(state) ==> pred(Executor.runOne(nop, state, choice)))

          Executor.runConsistentSubHistory(nop, schedule, history)
          nopDoesNothing(history.tail, schedule.tail)
        }
      }
    }.ensuring(
      Executor.historyMaintainsInvariant(pred, nop, history, schedule)
    )

    nopDoesNothing(res, schedule)
    Executor.predicateForAllPremiseTrue(pred, nop, s, res, schedule)
    assert(Executor.predicateForAll(pred, res))

    res
  }
}
