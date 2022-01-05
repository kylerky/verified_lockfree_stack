# The Structure of the Project

The reference implementation of the lock-free stack to be verified is
under the subproject `core` while the verified code is under the
subproject `verified`.

# How to Verify the Code Using Stainless

For some reasons, `sbt` is not able to locate the `StainlessPlugin` in
 public repositories, which makes us to run `stainless` manually.

Under the root directory of the project, run the following command:

```bash
stainless verified/src/main/scala/runtime/Executor.scala verified/src/main/scala/concurrent/TreiberStack.scala
```
