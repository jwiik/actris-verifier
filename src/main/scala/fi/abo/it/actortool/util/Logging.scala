package fi.abo.it.actortool.util

import java.io.PrintStream

object Log extends Logger(Console.err, 2)

class Logger(stream: PrintStream, level: Int) {
  
  object Level {
    val Error = 0
    val Warning = 1
    val Info = 2
    val Debug = 3
    val Verbose = 4
  }
  
  def verbose(msg: String) = print(Level.Verbose, msg)
  def debug(msg: String) = print(Level.Debug, msg)
  def info(msg: String) = print(Level.Info, msg)
  def warning(msg: String) = print(Level.Warning, msg)
  def error(msg: String) = print(Level.Error, msg)
  
  def print(msgLevel: Int, msg: String) {
    if (level <= msgLevel) stream.println(msg)
  }
  
}