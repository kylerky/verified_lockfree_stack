package treiber

import java.util.concurrent.atomic.AtomicReference

class TreiberStack[T] {
  private class Node(var next: Node, var data: T)

  private var head = new AtomicReference[Node]()

  def push(v: T): Unit = {
    val oldHead = head.get()
    val node = new Node(oldHead, v)
    if (!head.compareAndSet(oldHead, node)) {
      push(v)
    }
  }

  def pop(): Option[T] = {
    val oldHead = head.get()
    if (oldHead == null) {
      None
    } else {
      val newHead = oldHead.next
      if (head.compareAndSet(oldHead, newHead)) {
        Some(oldHead.data)
      } else {
        pop()
      }
    }
  }
}
