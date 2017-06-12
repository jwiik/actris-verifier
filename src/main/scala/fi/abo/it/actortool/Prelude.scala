package fi.abo.it.actortool

abstract class Prelude {
  
  private var components: Set[PreludeComponent] = defaultComponents
  
  def defaultComponents: Set[PreludeComponent]
  
  // adds component c to the prelude. has no effect if c is already present.
  def addComponent(c: PreludeComponent*): Unit = {
    for (comp <- c) {
      for (d <- comp.dependencies) {
        components = components + d
      }
      components = components + comp
    }
  }
  
  // removes a component from the prelude. use with great care, as other parts of
  // the system could depend on the component c being present in the prelude.
  def removeComponent(c: PreludeComponent*): Unit = {
    components = components -- c
  }
  
  // get the prelude (with all components currently included)
  def get: String = {
    var l = components.toList.sorted
    l.foldLeft("")((s:String,a:PreludeComponent) => s + a.text)
  }
  
}


trait PreludeOrder {
  val order: List[PreludeComponent]
}

abstract class PreludeComponent(preludeOrder: PreludeOrder) extends Ordered[PreludeComponent]  {
  
  def compare(that: PreludeComponent) = {
    if (!preludeOrder.order.contains(this) || !preludeOrder.order.contains(that)) { 
      throw new RuntimeException("Prelude components not properly set up: " + this + " " + that)
    }
    preludeOrder.order.indexOf(this) compare preludeOrder.order.indexOf(that)
  }

  def text: String
  def dependencies = Set.empty[PreludeComponent]
  override def toString = this.getClass.getSimpleName
}

