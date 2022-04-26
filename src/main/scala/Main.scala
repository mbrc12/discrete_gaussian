import org.jfree.graphics2d.svg._
import java.awt.Graphics2D
import java.awt.Color
import java.io.File

import scala.util.control.Breaks._
import scala.util.Random
import scala.collection.mutable.ArrayBuffer

case class Point(x : Int, y : Int)

val seed = 57575
given rng : Random = Random(seed)

object Config {
  val textMode = true
  val baseName = "output_swatch3_standard"
  val output = File(baseName + (if (textMode) "_labels" else "") + ".svg")
  val bgColor = Color.DARK_GRAY
  val fgColor = Color.BLACK

  val BETA = 0.2
  val width = 1000
  val height = 1000
  val latticeSize = 25
  val cellWidth = width / latticeSize
  val cellHeight = height / latticeSize
  val arcSize = 5
  val margin = 1
  val fontSize : Float = 15

  val fixedRow = (latticeSize/2).toInt
  val fixedCol = (latticeSize/2).toInt
  val fixedVal = 99
  val cutoff = fixedVal + 10

  val lattice = Array.ofDim[Point](latticeSize, latticeSize)

  for {
    (i, p) <- Range(0, latticeSize) zip LazyList.from(-latticeSize/2);
    (j, q) <- Range(0, latticeSize) zip LazyList.from(-latticeSize/2);
    x = width/2 + q * cellWidth;
    y = height/2 + p * cellHeight
  } lattice(i)(j) = Point(x, y)

  val tolerance = 1e-9.toDouble
  val inf = 1e9.toInt
}

@main def main() = {
  import Config._
  val svg = SVGGraphics2D(width, height)
  svg.setBackground(bgColor)

  val font = svg.getFont().deriveFont(fontSize)
  svg.setFont(font)

  svg.clearRect(0, 0, width, height)

  val dg = CFTP(cutoff)
  
  for {i <- 0 until latticeSize; j <- 0 until latticeSize} {
    svg.cell(dg(i, j), lattice(i)(j))
  }

  SVGUtils.writeToSVG(output, svg.getSVGElement)
}

// returns an exact sample from DG L
def CFTP(cutoff : Int) : DG = {
  import Config.{latticeSize => L, fixedRow, fixedCol, fixedVal}
  val random = LazyList.continually(Bits.sample(L))  

  val topInit = DG(L, cutoff) //.updated(fixedRow, fixedCol, fixedVal)
  val botInit = DG(L, -cutoff) //.updated(fixedRow, fixedCol, fixedVal)

  val computeFinal = (N : Int) => {
    val sample = random.take(N).foldLeft((topInit, botInit)){
      case ((top, bot), bits) => {
        // if (bits.row != fixedRow || bits.col != fixedCol) {
          val top1 = top.step(bits)
          val bot1 = bot.step(bits)
          (top1, bot1)
        // } else (top, bot)
    }}
    println(s" N = $N " + sample._1.ham_dist(sample._2))
    sample
  }

  LazyList.iterate(16)(_ * 2)
    .map(computeFinal)
    .dropWhile((top, bot) => top !== bot)
    .head._1
}

case class Bits(row : Int, col : Int, unif : Double)
object Bits {
  def sample(L : Int)(using rng : Random) : Bits = 
    Bits(rng.nextInt(L), rng.nextInt(L), rng.nextDouble())
}


class DG(val L : Int, val v : Int) { self => 

  type SpinLattice = Vector[Int]

  private var A : SpinLattice = Vector.fill(L * L)(v)

  def apply(i : Int, j : Int) = {
    if (i < 0 || i >= L || j < 0 || j >= L)
      0
    else 
      A(i * L + j)
  }

  def ham_dist(that : DG) : Int = {
    (self.A zip that.A).count((x, y) => x != y)
  }

  def ===(that : DG) : Boolean = {
    self.ham_dist(that) == 0
  }

  def !==(that : DG) : Boolean = !(self === that)

  override def toString() : String = A.toString

  private def copy(B : SpinLattice) : DG = {
    val dg = DG(L, 0)
    dg.A = B
    dg
  }

  def updatedSL(i : Int, j : Int, v : Int) : SpinLattice = {
    self.A.updated(i * L + j, v)
  }

  def updated(i : Int, j : Int, v : Int) : DG = {
    self.copy(self.updatedSL(i, j, v))
  }

  def step(bits : Bits) : DG = {
    import bits._
    val meas = cond(row, col)
    val newLattice = self.updatedSL(row, col, meas.sample(bits))
    self.copy(newLattice)
  }

  def cond(i : Int, j : Int) : DiscreteGaussian = {
    import Config.BETA
    DiscreteGaussian(((self(i - 1, j) + self(i + 1, j) + self(i, j - 1) + self(i, j + 1))/4).toDouble, 4*BETA)
  }
}


case class DiscreteGaussian(mu : Double, beta : Double) {

  // sample using the information in Bits
  def sample(bits : Bits) : Int = {
    import Config.{tolerance, inf}

    val mass : (Double => Double) = x => Math.exp(-beta * (x - mu) * (x - mu))

    val mu_rnd = Math.round(mu).toInt

    type Mass = (Int, Double)

    val weights = ArrayBuffer[Mass]()
    weights += mu_rnd -> mass(mu_rnd)

    var total = mass(mu_rnd)

    breakable {
      for (i <- LazyList.from(1)) {
        val neg = mu_rnd - i; val pos = mu_rnd + i
        val mass_neg = mass(neg); val mass_pos = mass(pos)
        val mass_add = mass_neg + mass_pos
        weights += neg -> mass_neg
        weights += pos -> mass_pos
        total += mass_add
        if (mass_add < tolerance * total) 
          break
      }
    }

    val unif = bits.unif

    weights.sorted.to(LazyList)
      .foldLeft(LazyList() :+ (-inf, 0.toDouble)){ case (pref, (x, p)) => pref :+ (x, p/total + pref.last._2) }
      .dropWhile(_._2 <= unif)
      .head._1
  }
}

object ColorGradient {
  type HSB = (Float, Float, Float)

  val high : HSB = (41.0f/360, 0.6f, 0.92f)
  val low : HSB = (268.0f/360, 0.37f, 0.31f)

  // maps -inf to inf to [0, 1] such that 0 is mapped to 1/2
  def curve(x : Float) : Float = ((Math.atan(x)*(2/Math.PI) + 1)/2).toFloat

  def interpolate(x : Float) : HSB = {
    val t = 1 - curve(x)
    (high._1 * (1 - t) + low._1 * t, high._2 * (1 - t) + low._2 * t, high._3 * (1 - t) + low._3 * t)
  }

  def colorOf(n : Int) : Color = {
    Color.getHSBColor.tupled(interpolate(n))
  }
}

// Not used
object ColorGradient2 {

  type HSB = Array[Float]

  // val colorSwatch : List[HSB] = 
  //   List(Array(268.0f/360, 0.37f, 0.31f), Array(41.0f/360, 0.6f, 0.92f))

  val colorSwatch : List[HSB] = 
    // List("#67001f","#b2182b","#d6604d","#f4a582","#fddbc7","#f7f7f7","#d1e5f0","#92c5de","#4393c3","#2166ac","#053061")
    // List("#f7fcf0","#e0f3db","#ccebc5","#a8ddb5","#7bccc4","#4eb3d3","#2b8cbe","#0868ac","#084081")
    // List("#001219","#005f73","#0a9396","#94d2bd","#e9d8a6","#ee9b00","#ca6702","#bb3e03","#ae2012","#9b2226")
    List("#fde725", "#addc30", "#5ec962", "#28ae80", "#21918c", "#2c728e", "#3b528b", "#472d7b", "#440154")
      .reverse
      .map(Color.decode)
      .map(c => Color.RGBtoHSB(c.getRed(), c.getGreen(), c.getBlue(), null))
  
  val N = colorSwatch.length

  def normalize(x : Double) = ((Math.atan(x) * (2/Math.PI) + 1)/2)
  def adjust(x : Double) = {
    if (x == 0) 0
    else if (x >= 1) Math.pow(Math.log(x), 1.5) + 0.5
    else x * 2
  }

  def curve(x : Double) : Float = normalize(adjust(x)).toFloat
  def mod1(x : Double) = if (x < 0) x + 1 else x

  // HSB color interpolator
  def interpolate(a : HSB, b : HSB, t : Float) : Color = {
    var ha = a(0)
    var hb = b(0)
    var d = hb - ha
    if (ha > hb) {
      interpolate(b, a, 1 - t)
    } else {
      val h : Double = 
        if (d > 0.5) {
          ha = ha + 1
          mod1(ha + t * (hb - ha))
        } 
        else ha + t * d

      val sb = (a.tail zip b.tail).map((p, q) => p * t + q * (1 - t)).toArray
      Color.getHSBColor(h.toFloat, sb(0), sb(1))
    }
  }

  def colorOf(n : Int) : Color = {
    val t0 = curve(n)
    val i = Math.floor(t0 * (N - 1)).toInt
    val t = (t0 - i/(N - 1)).toFloat
    interpolate(colorSwatch(i), colorSwatch(i + 1), t) 
  }
}

extension (g : Graphics2D) {

  // c is the location of the center
  def cell(n : Int, c : Point) = { 
    import Config._
    import ColorGradient.colorOf

    val color = colorOf(n)
    g.setPaint(color)

    val topX = c.x - cellWidth/2 + margin
    val topY = c.y - cellHeight/2 + margin

    g.fillRoundRect(topX, topY, cellWidth - 2 * margin, cellHeight - 2 * margin, arcSize, arcSize)

    val fontMetrics = g.getFontMetrics
    val text = n.toString
    val bounds = fontMetrics.getStringBounds(text, g)

    val posX = Math.round(c.x - bounds.getWidth/2)
    val posY = Math.round(c.y - bounds.getHeight/2 + fontMetrics.getAscent)

    g.setPaint(fgColor)
    if (textMode) {
      g.drawString(text, posX, posY)
    }
  }
}


