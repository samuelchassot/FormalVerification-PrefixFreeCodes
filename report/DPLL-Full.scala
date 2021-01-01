private[this] def search(): Results.Result = {
  val topLevelStopWatch = StopWatch("toplevelloop")
  val deduceStopWatch = StopWatch("deduce")
  val decideStopWatch = StopWatch("decide")
  val backtrackStopWatch = StopWatch("backtrack")
  
  topLevelStopWatch.time {
    deduceStopWatch.time {
      deduce()
    }
    if(status == Conflict)
      status = Unsatisfiable
    val timeout: Option[Int] = Settings.timeout
    var elapsedTime: Long = 0 //in ms
    while(status == Unknown) {
      val startTime = System.currentTimeMillis
      decideStopWatch.time {
        decide()
      }
      var cont = true
      while(cont) {
        deduceStopWatch.time {
          deduce()
        }
        
        if(status == Conflict) {
          backtrackStopWatch.time {
            backtrack()
          }
        } else {
          cont = false
        }
      }
      val endTime = System.currentTimeMillis
      elapsedTime += (endTime - startTime)
      timeout.foreach(timeout => if(elapsedTime > 1000*timeout)
        status = Timeout)
    }
  }
  status match {
    case Unknown | Conflict => sys.error("unexpected")
    case Timeout => Results.Unknown
    case Unsatisfiable => Results.Unsatisfiable
    case Satisfiable => Results.Satisfiable(model.map(pol => pol==1))
  }  
}
