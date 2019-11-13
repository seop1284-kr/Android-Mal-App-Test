private def processWU: WorkUnit[T, S] => Unit = { wu =>
  if (wu.needProcess(handler)) {
    try {
      wu.initFn()
      if (wu.needHeapSummary) {
        generateHeapSummary(wu.method) match {
          case Some(w) =>
            wu match {
              case dfw: DataFlowWu[T, S] =>
                  dfw.setIDFG(w.getIDFG, w.getHeapMap)
              case _ =>
            }
          case None =>
        }
      }
      val summary = wu.generateSummary(suGen)
      sm.register(wu.method.getSignature, summary)
    } catch {
      case e: Exception =>
        if(debug) {
          e.printStackTrace()
        }
    } finally {
      wu.finalFn()
    }
  }
}