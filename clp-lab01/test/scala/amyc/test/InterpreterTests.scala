package amyc
package test

import utils.Frontend
import interpreter.Interpreter

class InterpreterTests extends ExecutionTests {
  val pipeline = Frontend.pipeline andThen Interpreter
}
