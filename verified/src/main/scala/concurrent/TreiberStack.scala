package concurrent

import stainless.lang._
import stainless.collection._

import runtime.Executor
import runtime.Executor.{State, Schedule, History}

object TreiberStack {
  type Shared = Int
  type TaskState = Int
  type StackState = State[Shared, TaskState]

  val f = (x: Int, y: Int) => (x, y)

  // val initState: State[Int, Int] = State(0, List(0, 0))

  def run(schedule: Schedule, s: StackState): List[StackState] = {
    require(Executor.scheduleValid(schedule, s))

    val pred = (s0: StackState) => s0 == s

    val res = Executor
      .runMaintainsInvariant(pred, f, s, schedule)

    def fDoNothing(
        history: History[Shared, TaskState],
        schedule: Schedule
    ): Unit = {
      require(history.nonEmpty)
      require(Executor.runConsistent(f, schedule, history))

      schedule match {
        case Nil() =>
        case Cons(choice, rest) => {
          assert(Executor.choiceValid(choice, history.head))
          val state = history.head
          val newState = Executor.runOne(f, state, choice)
          assert(newState.shared == state.shared)
          assert(newState.tasks.length == state.tasks.length)
          assert(newState == state)
          assert(pred(state) ==> pred(Executor.runOne(f, state, choice)))
          fDoNothing(history.tail, schedule.tail)
        }
      }
    }.ensuring(
      Executor.historyMaintainsInvariant(pred, f, history, schedule)
    )

    fDoNothing(res, schedule)
    Executor.predicateForAllPremiseTrue(pred, f, s, res, schedule)
    assert(Executor.predicateForAll(pred, res))

    res
  }

}
