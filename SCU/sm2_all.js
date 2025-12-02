function _typeof(obj) { "@babel/helpers - typeof"; if (typeof Symbol === "function" && typeof Symbol.iterator === "symbol") { _typeof = function _typeof(obj) { return typeof obj; }; } else { _typeof = function _typeof(obj) { return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj; }; } return _typeof(obj); }

/**
 SM2 v1.0
 ct 20170215

 代码加密步骤：
 1、加密压缩
 2、混淆
 */

/*
*
* jsbn
*
*
* */

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.
// Basic JavaScript BN library - subset useful for RSA encryption.
// Bits per digit
var dbits; // JavaScript engine analysis

var canary = 0xdeadbeefcafe;
var j_lm = (canary & 0xffffff) == 0xefcafe; // (public) Constructor

function BigInteger(a, b, c) {
  if (a != null) if ("number" == typeof a) this.fromNumber(a, b, c);else if (b == null && "string" != typeof a) this.fromString(a, 256);else this.fromString(a, b);
} // return new, unset BigInteger


function nbi() {
  return new BigInteger(null);
} // am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.
// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)


function am1(i, x, w, j, c, n) {
  while (--n >= 0) {
    var v = x * this[i++] + w[j] + c;
    c = Math.floor(v / 0x4000000);
    w[j++] = v & 0x3ffffff;
  }

  return c;
} // am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)


function am2(i, x, w, j, c, n) {
  var xl = x & 0x7fff,
      xh = x >> 15;

  while (--n >= 0) {
    var l = this[i] & 0x7fff;
    var h = this[i++] >> 15;
    var m = xh * l + h * xl;
    l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
    c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
    w[j++] = l & 0x3fffffff;
  }

  return c;
} // Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.


function am3(i, x, w, j, c, n) {
  var xl = x & 0x3fff,
      xh = x >> 14;

  while (--n >= 0) {
    var l = this[i] & 0x3fff;
    var h = this[i++] >> 14;
    var m = xh * l + h * xl;
    l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
    c = (l >> 28) + (m >> 14) + xh * h;
    w[j++] = l & 0xfffffff;
  }

  return c;
}

if (j_lm && navigator.appName == "Microsoft Internet Explorer") {
  BigInteger.prototype.am = am2;
  dbits = 30;
} else if (j_lm && navigator.appName != "Netscape") {
  BigInteger.prototype.am = am1;
  dbits = 26;
} else {
  // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = (1 << dbits) - 1;
BigInteger.prototype.DV = 1 << dbits;
var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2, BI_FP);
BigInteger.prototype.F1 = BI_FP - dbits;
BigInteger.prototype.F2 = 2 * dbits - BI_FP; // Digit conversions

var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr, vv;
rr = "0".charCodeAt(0);

for (vv = 0; vv <= 9; ++vv) {
  BI_RC[rr++] = vv;
}

rr = "a".charCodeAt(0);

for (vv = 10; vv < 36; ++vv) {
  BI_RC[rr++] = vv;
}

rr = "A".charCodeAt(0);

for (vv = 10; vv < 36; ++vv) {
  BI_RC[rr++] = vv;
}

function int2char(n) {
  return BI_RM.charAt(n);
}

function intAt(s, i) {
  var c = BI_RC[s.charCodeAt(i)];
  return c == null ? -1 : c;
} // (protected) copy this to r


function bnpCopyTo(r) {
  for (var i = this.t - 1; i >= 0; --i) {
    r[i] = this[i];
  }

  r.t = this.t;
  r.s = this.s;
} // (protected) set from integer value x, -DV <= x < DV


function bnpFromInt(x) {
  this.t = 1;
  this.s = x < 0 ? -1 : 0;
  if (x > 0) this[0] = x;else if (x < -1) this[0] = x + this.DV;else this.t = 0;
} // return bigint initialized to value


function nbv(i) {
  var r = nbi();
  r.fromInt(i);
  return r;
} // (protected) set from string and radix


function bnpFromString(s, b) {
  var k;
  if (b == 16) k = 4;else if (b == 8) k = 3;else if (b == 256) k = 8; // byte array
  else if (b == 2) k = 1;else if (b == 32) k = 5;else if (b == 4) k = 2;else {
      this.fromRadix(s, b);
      return;
    }
  this.t = 0;
  this.s = 0;
  var i = s.length,
      mi = false,
      sh = 0;

  while (--i >= 0) {
    var x = k == 8 ? s[i] & 0xff : intAt(s, i);

    if (x < 0) {
      if (s.charAt(i) == "-") mi = true;
      continue;
    }

    mi = false;
    if (sh == 0) this[this.t++] = x;else if (sh + k > this.DB) {
      this[this.t - 1] |= (x & (1 << this.DB - sh) - 1) << sh;
      this[this.t++] = x >> this.DB - sh;
    } else this[this.t - 1] |= x << sh;
    sh += k;
    if (sh >= this.DB) sh -= this.DB;
  }

  if (k == 8 && (s[0] & 0x80) != 0) {
    this.s = -1;
    if (sh > 0) this[this.t - 1] |= (1 << this.DB - sh) - 1 << sh;
  }

  this.clamp();
  if (mi) BigInteger.ZERO.subTo(this, this);
} // (protected) clamp off excess high words


function bnpClamp() {
  var c = this.s & this.DM;

  while (this.t > 0 && this[this.t - 1] == c) {
    --this.t;
  }
} // (public) return string representation in given radix


function bnToString(b) {
  if (this.s < 0) return "-" + this.negate().toString(b);
  var k;
  if (b == 16) k = 4;else if (b == 8) k = 3;else if (b == 2) k = 1;else if (b == 32) k = 5;else if (b == 4) k = 2;else return this.toRadix(b);
  var km = (1 << k) - 1,
      d,
      m = false,
      r = "",
      i = this.t;
  var p = this.DB - i * this.DB % k;

  if (i-- > 0) {
    if (p < this.DB && (d = this[i] >> p) > 0) {
      m = true;
      r = int2char(d);
    }

    while (i >= 0) {
      if (p < k) {
        d = (this[i] & (1 << p) - 1) << k - p;
        d |= this[--i] >> (p += this.DB - k);
      } else {
        d = this[i] >> (p -= k) & km;

        if (p <= 0) {
          p += this.DB;
          --i;
        }
      }

      if (d > 0) m = true;
      if (m) r += int2char(d);
    }
  }

  return m ? r : "0";
} // (public) -this


function bnNegate() {
  var r = nbi();
  BigInteger.ZERO.subTo(this, r);
  return r;
} // (public) |this|


function bnAbs() {
  return this.s < 0 ? this.negate() : this;
} // (public) return + if this > a, - if this < a, 0 if equal


function bnCompareTo(a) {
  var r = this.s - a.s;
  if (r != 0) return r;
  var i = this.t;
  r = i - a.t;
  if (r != 0) return this.s < 0 ? -r : r;

  while (--i >= 0) {
    if ((r = this[i] - a[i]) != 0) return r;
  }

  return 0;
} // returns bit length of the integer x


function nbits(x) {
  var r = 1,
      t;

  if ((t = x >>> 16) != 0) {
    x = t;
    r += 16;
  }

  if ((t = x >> 8) != 0) {
    x = t;
    r += 8;
  }

  if ((t = x >> 4) != 0) {
    x = t;
    r += 4;
  }

  if ((t = x >> 2) != 0) {
    x = t;
    r += 2;
  }

  if ((t = x >> 1) != 0) {
    x = t;
    r += 1;
  }

  return r;
} // (public) return the number of bits in "this"


function bnBitLength() {
  if (this.t <= 0) return 0;
  return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ this.s & this.DM);
} // (protected) r = this << n*DB


function bnpDLShiftTo(n, r) {
  var i;

  for (i = this.t - 1; i >= 0; --i) {
    r[i + n] = this[i];
  }

  for (i = n - 1; i >= 0; --i) {
    r[i] = 0;
  }

  r.t = this.t + n;
  r.s = this.s;
} // (protected) r = this >> n*DB


function bnpDRShiftTo(n, r) {
  for (var i = n; i < this.t; ++i) {
    r[i - n] = this[i];
  }

  r.t = Math.max(this.t - n, 0);
  r.s = this.s;
} // (protected) r = this << n


function bnpLShiftTo(n, r) {
  var bs = n % this.DB;
  var cbs = this.DB - bs;
  var bm = (1 << cbs) - 1;
  var ds = Math.floor(n / this.DB),
      c = this.s << bs & this.DM,
      i;

  for (i = this.t - 1; i >= 0; --i) {
    r[i + ds + 1] = this[i] >> cbs | c;
    c = (this[i] & bm) << bs;
  }

  for (i = ds - 1; i >= 0; --i) {
    r[i] = 0;
  }

  r[ds] = c;
  r.t = this.t + ds + 1;
  r.s = this.s;
  r.clamp();
} // (protected) r = this >> n


function bnpRShiftTo(n, r) {
  r.s = this.s;
  var ds = Math.floor(n / this.DB);

  if (ds >= this.t) {
    r.t = 0;
    return;
  }

  var bs = n % this.DB;
  var cbs = this.DB - bs;
  var bm = (1 << bs) - 1;
  r[0] = this[ds] >> bs;

  for (var i = ds + 1; i < this.t; ++i) {
    r[i - ds - 1] |= (this[i] & bm) << cbs;
    r[i - ds] = this[i] >> bs;
  }

  if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
  r.t = this.t - ds;
  r.clamp();
} // (protected) r = this - a


function bnpSubTo(a, r) {
  var i = 0,
      c = 0,
      m = Math.min(a.t, this.t);

  while (i < m) {
    c += this[i] - a[i];
    r[i++] = c & this.DM;
    c >>= this.DB;
  }

  if (a.t < this.t) {
    c -= a.s;

    while (i < this.t) {
      c += this[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }

    c += this.s;
  } else {
    c += this.s;

    while (i < a.t) {
      c -= a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }

    c -= a.s;
  }

  r.s = c < 0 ? -1 : 0;
  if (c < -1) r[i++] = this.DV + c;else if (c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
} // (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.


function bnpMultiplyTo(a, r) {
  var x = this.abs(),
      y = a.abs();
  var i = x.t;
  r.t = i + y.t;

  while (--i >= 0) {
    r[i] = 0;
  }

  for (i = 0; i < y.t; ++i) {
    r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
  }

  r.s = 0;
  r.clamp();
  if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
} // (protected) r = this^2, r != this (HAC 14.16)


function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2 * x.t;

  while (--i >= 0) {
    r[i] = 0;
  }

  for (i = 0; i < x.t - 1; ++i) {
    var c = x.am(i, x[i], r, 2 * i, 0, 1);

    if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
      r[i + x.t] -= x.DV;
      r[i + x.t + 1] = 1;
    }
  }

  if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
  r.s = 0;
  r.clamp();
} // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.


function bnpDivRemTo(m, q, r) {
  var pm = m.abs();
  if (pm.t <= 0) return;
  var pt = this.abs();

  if (pt.t < pm.t) {
    if (q != null) q.fromInt(0);
    if (r != null) this.copyTo(r);
    return;
  }

  if (r == null) r = nbi();
  var y = nbi(),
      ts = this.s,
      ms = m.s;
  var nsh = this.DB - nbits(pm[pm.t - 1]); // normalize modulus

  if (nsh > 0) {
    pm.lShiftTo(nsh, y);
    pt.lShiftTo(nsh, r);
  } else {
    pm.copyTo(y);
    pt.copyTo(r);
  }

  var ys = y.t;
  var y0 = y[ys - 1];
  if (y0 == 0) return;
  var yt = y0 * (1 << this.F1) + (ys > 1 ? y[ys - 2] >> this.F2 : 0);
  var d1 = this.FV / yt,
      d2 = (1 << this.F1) / yt,
      e = 1 << this.F2;
  var i = r.t,
      j = i - ys,
      t = q == null ? nbi() : q;
  y.dlShiftTo(j, t);

  if (r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t, r);
  }

  BigInteger.ONE.dlShiftTo(ys, t);
  t.subTo(y, y); // "negative" y so we can replace sub with am later

  while (y.t < ys) {
    y[y.t++] = 0;
  }

  while (--j >= 0) {
    // Estimate quotient digit
    var qd = r[--i] == y0 ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);

    if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {
      // Try it out
      y.dlShiftTo(j, t);
      r.subTo(t, r);

      while (r[i] < --qd) {
        r.subTo(t, r);
      }
    }
  }

  if (q != null) {
    r.drShiftTo(ys, q);
    if (ts != ms) BigInteger.ZERO.subTo(q, q);
  }

  r.t = ys;
  r.clamp();
  if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder

  if (ts < 0) BigInteger.ZERO.subTo(r, r);
} // (public) this mod a


function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a, null, r);
  if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
  return r;
} // Modular reduction using "classic" algorithm


function Classic(m) {
  this.m = m;
}

function cConvert(x) {
  if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);else return x;
}

function cRevert(x) {
  return x;
}

function cReduce(x) {
  x.divRemTo(this.m, null, x);
}

function cMulTo(x, y, r) {
  x.multiplyTo(y, r);
  this.reduce(r);
}

function cSqrTo(x, r) {
  x.squareTo(r);
  this.reduce(r);
}

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo; // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.

function bnpInvDigit() {
  if (this.t < 1) return 0;
  var x = this[0];
  if ((x & 1) == 0) return 0;
  var y = x & 3; // y == 1/x mod 2^2

  y = y * (2 - (x & 0xf) * y) & 0xf; // y == 1/x mod 2^4

  y = y * (2 - (x & 0xff) * y) & 0xff; // y == 1/x mod 2^8

  y = y * (2 - ((x & 0xffff) * y & 0xffff)) & 0xffff; // y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints

  y = y * (2 - x * y % this.DV) % this.DV; // y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV

  return y > 0 ? this.DV - y : -y;
} // Montgomery reduction


function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp & 0x7fff;
  this.mph = this.mp >> 15;
  this.um = (1 << m.DB - 15) - 1;
  this.mt2 = 2 * m.t;
} // xR mod m


function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t, r);
  r.divRemTo(this.m, null, r);
  if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
  return r;
} // x/R mod m


function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
} // x = x/R mod m (HAC 14.32)


function montReduce(x) {
  while (x.t <= this.mt2) {
    // pad x so am has enough room later
    x[x.t++] = 0;
  }

  for (var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i] & 0x7fff;
    var u0 = j * this.mpl + ((j * this.mph + (x[i] >> 15) * this.mpl & this.um) << 15) & x.DM; // use am to combine the multiply-shift-add into one call

    j = i + this.m.t;
    x[j] += this.m.am(0, u0, x, i, 0, this.m.t); // propagate carry

    while (x[j] >= x.DV) {
      x[j] -= x.DV;
      x[++j]++;
    }
  }

  x.clamp();
  x.drShiftTo(this.m.t, x);
  if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
} // r = "x^2/R mod m"; x != r


function montSqrTo(x, r) {
  x.squareTo(r);
  this.reduce(r);
} // r = "xy/R mod m"; x,y != r


function montMulTo(x, y, r) {
  x.multiplyTo(y, r);
  this.reduce(r);
}

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo; // (protected) true iff this is even

function bnpIsEven() {
  return (this.t > 0 ? this[0] & 1 : this.s) == 0;
} // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)


function bnpExp(e, z) {
  if (e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(),
      r2 = nbi(),
      g = z.convert(this),
      i = nbits(e) - 1;
  g.copyTo(r);

  while (--i >= 0) {
    z.sqrTo(r, r2);
    if ((e & 1 << i) > 0) z.mulTo(r2, g, r);else {
      var t = r;
      r = r2;
      r2 = t;
    }
  }

  return z.revert(r);
} // (public) this^e % m, 0 <= e < 2^32


function bnModPowInt(e, m) {
  var z;
  if (e < 256 || m.isEven()) z = new Classic(m);else z = new Montgomery(m);
  return this.exp(e, z);
} // protected


BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp; // public

BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt; // "constants"

BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
/*
*
*
* jsbn2
*
* */

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Copyright (c) 2005-2009  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.
// Extended JavaScript BN functions, required for RSA private ops.
// Version 1.1: new BigInteger("0", 10) returns "proper" zero
// Version 1.2: square() API, isProbablePrime fix
// (public)

function bnClone() {
  var r = nbi();
  this.copyTo(r);
  return r;
} // (public) return value as integer


function bnIntValue() {
  if (this.s < 0) {
    if (this.t == 1) return this[0] - this.DV;else if (this.t == 0) return -1;
  } else if (this.t == 1) return this[0];else if (this.t == 0) return 0; // assumes 16 < DB < 32


  return (this[1] & (1 << 32 - this.DB) - 1) << this.DB | this[0];
} // (public) return value as byte


function bnByteValue() {
  return this.t == 0 ? this.s : this[0] << 24 >> 24;
} // (public) return value as short (assumes DB>=16)


function bnShortValue() {
  return this.t == 0 ? this.s : this[0] << 16 >> 16;
} // (protected) return x s.t. r^x < DV


function bnpChunkSize(r) {
  return Math.floor(Math.LN2 * this.DB / Math.log(r));
} // (public) 0 if this == 0, 1 if this > 0


function bnSigNum() {
  if (this.s < 0) return -1;else if (this.t <= 0 || this.t == 1 && this[0] <= 0) return 0;else return 1;
} // (protected) convert to radix string


function bnpToRadix(b) {
  if (b == null) b = 10;
  if (this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b, cs);
  var d = nbv(a),
      y = nbi(),
      z = nbi(),
      r = "";
  this.divRemTo(d, y, z);

  while (y.signum() > 0) {
    r = (a + z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d, y, z);
  }

  return z.intValue().toString(b) + r;
} // (protected) convert from radix string


function bnpFromRadix(s, b) {
  this.fromInt(0);
  if (b == null) b = 10;
  var cs = this.chunkSize(b);
  var d = Math.pow(b, cs),
      mi = false,
      j = 0,
      w = 0;

  for (var i = 0; i < s.length; ++i) {
    var x = intAt(s, i);

    if (x < 0) {
      if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
      continue;
    }

    w = b * w + x;

    if (++j >= cs) {
      this.dMultiply(d);
      this.dAddOffset(w, 0);
      j = 0;
      w = 0;
    }
  }

  if (j > 0) {
    this.dMultiply(Math.pow(b, j));
    this.dAddOffset(w, 0);
  }

  if (mi) BigInteger.ZERO.subTo(this, this);
} // (protected) alternate constructor


function bnpFromNumber(a, b, c) {
  if ("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if (a < 2) this.fromInt(1);else {
      this.fromNumber(a, c);
      if (!this.testBit(a - 1)) // force MSB set
        this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
      if (this.isEven()) this.dAddOffset(1, 0); // force odd

      while (!this.isProbablePrime(b)) {
        this.dAddOffset(2, 0);
        if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
      }
    }
  } else {
    // new BigInteger(int,RNG)
    var x = new Array(),
        t = a & 7;
    x.length = (a >> 3) + 1;
    b.nextBytes(x);
    if (t > 0) x[0] &= (1 << t) - 1;else x[0] = 0;
    this.fromString(x, 256);
  }
} // (public) convert to bigendian byte array


function bnToByteArray() {
  var i = this.t,
      r = new Array();
  r[0] = this.s;
  var p = this.DB - i * this.DB % 8,
      d,
      k = 0;

  if (i-- > 0) {
    if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p) r[k++] = d | this.s << this.DB - p;

    while (i >= 0) {
      if (p < 8) {
        d = (this[i] & (1 << p) - 1) << 8 - p;
        d |= this[--i] >> (p += this.DB - 8);
      } else {
        d = this[i] >> (p -= 8) & 0xff;

        if (p <= 0) {
          p += this.DB;
          --i;
        }
      }

      if ((d & 0x80) != 0) d |= -256;
      if (k == 0 && (this.s & 0x80) != (d & 0x80)) ++k;
      if (k > 0 || d != this.s) r[k++] = d;
    }
  }

  return r;
}

function bnEquals(a) {
  return this.compareTo(a) == 0;
}

function bnMin(a) {
  return this.compareTo(a) < 0 ? this : a;
}

function bnMax(a) {
  return this.compareTo(a) > 0 ? this : a;
} // (protected) r = this op a (bitwise)


function bnpBitwiseTo(a, op, r) {
  var i,
      f,
      m = Math.min(a.t, this.t);

  for (i = 0; i < m; ++i) {
    r[i] = op(this[i], a[i]);
  }

  if (a.t < this.t) {
    f = a.s & this.DM;

    for (i = m; i < this.t; ++i) {
      r[i] = op(this[i], f);
    }

    r.t = this.t;
  } else {
    f = this.s & this.DM;

    for (i = m; i < a.t; ++i) {
      r[i] = op(f, a[i]);
    }

    r.t = a.t;
  }

  r.s = op(this.s, a.s);
  r.clamp();
} // (public) this & a


function op_and(x, y) {
  return x & y;
}

function bnAnd(a) {
  var r = nbi();
  this.bitwiseTo(a, op_and, r);
  return r;
} // (public) this | a


function op_or(x, y) {
  return x | y;
}

function bnOr(a) {
  var r = nbi();
  this.bitwiseTo(a, op_or, r);
  return r;
} // (public) this ^ a


function op_xor(x, y) {
  return x ^ y;
}

function bnXor(a) {
  var r = nbi();
  this.bitwiseTo(a, op_xor, r);
  return r;
} // (public) this & ~a


function op_andnot(x, y) {
  return x & ~y;
}

function bnAndNot(a) {
  var r = nbi();
  this.bitwiseTo(a, op_andnot, r);
  return r;
} // (public) ~this


function bnNot() {
  var r = nbi();

  for (var i = 0; i < this.t; ++i) {
    r[i] = this.DM & ~this[i];
  }

  r.t = this.t;
  r.s = ~this.s;
  return r;
} // (public) this << n


function bnShiftLeft(n) {
  var r = nbi();
  if (n < 0) this.rShiftTo(-n, r);else this.lShiftTo(n, r);
  return r;
} // (public) this >> n


function bnShiftRight(n) {
  var r = nbi();
  if (n < 0) this.lShiftTo(-n, r);else this.rShiftTo(n, r);
  return r;
} // return index of lowest 1-bit in x, x < 2^31


function lbit(x) {
  if (x == 0) return -1;
  var r = 0;

  if ((x & 0xffff) == 0) {
    x >>= 16;
    r += 16;
  }

  if ((x & 0xff) == 0) {
    x >>= 8;
    r += 8;
  }

  if ((x & 0xf) == 0) {
    x >>= 4;
    r += 4;
  }

  if ((x & 3) == 0) {
    x >>= 2;
    r += 2;
  }

  if ((x & 1) == 0) ++r;
  return r;
} // (public) returns index of lowest 1-bit (or -1 if none)


function bnGetLowestSetBit() {
  for (var i = 0; i < this.t; ++i) {
    if (this[i] != 0) return i * this.DB + lbit(this[i]);
  }

  if (this.s < 0) return this.t * this.DB;
  return -1;
} // return number of 1 bits in x


function cbit(x) {
  var r = 0;

  while (x != 0) {
    x &= x - 1;
    ++r;
  }

  return r;
} // (public) return number of set bits


function bnBitCount() {
  var r = 0,
      x = this.s & this.DM;

  for (var i = 0; i < this.t; ++i) {
    r += cbit(this[i] ^ x);
  }

  return r;
} // (public) true iff nth bit is set


function bnTestBit(n) {
  var j = Math.floor(n / this.DB);
  if (j >= this.t) return this.s != 0;
  return (this[j] & 1 << n % this.DB) != 0;
} // (protected) this op (1<<n)


function bnpChangeBit(n, op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r, op, r);
  return r;
} // (public) this | (1<<n)


function bnSetBit(n) {
  return this.changeBit(n, op_or);
} // (public) this & ~(1<<n)


function bnClearBit(n) {
  return this.changeBit(n, op_andnot);
} // (public) this ^ (1<<n)


function bnFlipBit(n) {
  return this.changeBit(n, op_xor);
} // (protected) r = this + a


function bnpAddTo(a, r) {
  var i = 0,
      c = 0,
      m = Math.min(a.t, this.t);

  while (i < m) {
    c += this[i] + a[i];
    r[i++] = c & this.DM;
    c >>= this.DB;
  }

  if (a.t < this.t) {
    c += a.s;

    while (i < this.t) {
      c += this[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }

    c += this.s;
  } else {
    c += this.s;

    while (i < a.t) {
      c += a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }

    c += a.s;
  }

  r.s = c < 0 ? -1 : 0;
  if (c > 0) r[i++] = c;else if (c < -1) r[i++] = this.DV + c;
  r.t = i;
  r.clamp();
} // (public) this + a


function bnAdd(a) {
  var r = nbi();
  this.addTo(a, r);
  return r;
} // (public) this - a


function bnSubtract(a) {
  var r = nbi();
  this.subTo(a, r);
  return r;
} // (public) this * a


function bnMultiply(a) {
  var r = nbi();
  this.multiplyTo(a, r);
  return r;
} // (public) this^2


function bnSquare() {
  var r = nbi();
  this.squareTo(r);
  return r;
} // (public) this / a


function bnDivide(a) {
  var r = nbi();
  this.divRemTo(a, r, null);
  return r;
} // (public) this % a


function bnRemainder(a) {
  var r = nbi();
  this.divRemTo(a, null, r);
  return r;
} // (public) [this/a,this%a]


function bnDivideAndRemainder(a) {
  var q = nbi(),
      r = nbi();
  this.divRemTo(a, q, r);
  return new Array(q, r);
} // (protected) this *= n, this >= 0, 1 < n < DV


function bnpDMultiply(n) {
  this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
  ++this.t;
  this.clamp();
} // (protected) this += n << w words, this >= 0


function bnpDAddOffset(n, w) {
  if (n == 0) return;

  while (this.t <= w) {
    this[this.t++] = 0;
  }

  this[w] += n;

  while (this[w] >= this.DV) {
    this[w] -= this.DV;
    if (++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
} // A "null" reducer


function NullExp() {}

function nNop(x) {
  return x;
}

function nMulTo(x, y, r) {
  x.multiplyTo(y, r);
}

function nSqrTo(x, r) {
  x.squareTo(r);
}

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo; // (public) this^e

function bnPow(e) {
  return this.exp(e, new NullExp());
} // (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.


function bnpMultiplyLowerTo(a, n, r) {
  var i = Math.min(this.t + a.t, n);
  r.s = 0; // assumes a,this >= 0

  r.t = i;

  while (i > 0) {
    r[--i] = 0;
  }

  var j;

  for (j = r.t - this.t; i < j; ++i) {
    r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
  }

  for (j = Math.min(a.t, n); i < j; ++i) {
    this.am(0, a[i], r, i, 0, n - i);
  }

  r.clamp();
} // (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.


function bnpMultiplyUpperTo(a, n, r) {
  --n;
  var i = r.t = this.t + a.t - n;
  r.s = 0; // assumes a,this >= 0

  while (--i >= 0) {
    r[i] = 0;
  }

  for (i = Math.max(n - this.t, 0); i < a.t; ++i) {
    r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
  }

  r.clamp();
  r.drShiftTo(1, r);
} // Barrett modular reduction


function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);else if (x.compareTo(this.m) < 0) return x;else {
    var r = nbi();
    x.copyTo(r);
    this.reduce(r);
    return r;
  }
}

function barrettRevert(x) {
  return x;
} // x = x mod m (HAC 14.42)


function barrettReduce(x) {
  x.drShiftTo(this.m.t - 1, this.r2);

  if (x.t > this.m.t + 1) {
    x.t = this.m.t + 1;
    x.clamp();
  }

  this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
  this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);

  while (x.compareTo(this.r2) < 0) {
    x.dAddOffset(1, this.m.t + 1);
  }

  x.subTo(this.r2, x);

  while (x.compareTo(this.m) >= 0) {
    x.subTo(this.m, x);
  }
} // r = x^2 mod m; x != r


function barrettSqrTo(x, r) {
  x.squareTo(r);
  this.reduce(r);
} // r = x*y mod m; x,y != r


function barrettMulTo(x, y, r) {
  x.multiplyTo(y, r);
  this.reduce(r);
}

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo; // (public) this^e % m (HAC 14.85)

function bnModPow(e, m) {
  var i = e.bitLength(),
      k,
      r = nbv(1),
      z;
  if (i <= 0) return r;else if (i < 18) k = 1;else if (i < 48) k = 3;else if (i < 144) k = 4;else if (i < 768) k = 5;else k = 6;
  if (i < 8) z = new Classic(m);else if (m.isEven()) z = new Barrett(m);else z = new Montgomery(m); // precomputation

  var g = new Array(),
      n = 3,
      k1 = k - 1,
      km = (1 << k) - 1;
  g[1] = z.convert(this);

  if (k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1], g2);

    while (n <= km) {
      g[n] = nbi();
      z.mulTo(g2, g[n - 2], g[n]);
      n += 2;
    }
  }

  var j = e.t - 1,
      w,
      is1 = true,
      r2 = nbi(),
      t;
  i = nbits(e[j]) - 1;

  while (j >= 0) {
    if (i >= k1) w = e[j] >> i - k1 & km;else {
      w = (e[j] & (1 << i + 1) - 1) << k1 - i;
      if (j > 0) w |= e[j - 1] >> this.DB + i - k1;
    }
    n = k;

    while ((w & 1) == 0) {
      w >>= 1;
      --n;
    }

    if ((i -= n) < 0) {
      i += this.DB;
      --j;
    }

    if (is1) {
      // ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    } else {
      while (n > 1) {
        z.sqrTo(r, r2);
        z.sqrTo(r2, r);
        n -= 2;
      }

      if (n > 0) z.sqrTo(r, r2);else {
        t = r;
        r = r2;
        r2 = t;
      }
      z.mulTo(r2, g[w], r);
    }

    while (j >= 0 && (e[j] & 1 << i) == 0) {
      z.sqrTo(r, r2);
      t = r;
      r = r2;
      r2 = t;

      if (--i < 0) {
        i = this.DB - 1;
        --j;
      }
    }
  }

  return z.revert(r);
} // (public) gcd(this,a) (HAC 14.54)


function bnGCD(a) {
  var x = this.s < 0 ? this.negate() : this.clone();
  var y = a.s < 0 ? a.negate() : a.clone();

  if (x.compareTo(y) < 0) {
    var t = x;
    x = y;
    y = t;
  }

  var i = x.getLowestSetBit(),
      g = y.getLowestSetBit();
  if (g < 0) return x;
  if (i < g) g = i;

  if (g > 0) {
    x.rShiftTo(g, x);
    y.rShiftTo(g, y);
  }

  while (x.signum() > 0) {
    if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
    if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);

    if (x.compareTo(y) >= 0) {
      x.subTo(y, x);
      x.rShiftTo(1, x);
    } else {
      y.subTo(x, y);
      y.rShiftTo(1, y);
    }
  }

  if (g > 0) y.lShiftTo(g, y);
  return y;
} // (protected) this % n, n < 2^26


function bnpModInt(n) {
  if (n <= 0) return 0;
  var d = this.DV % n,
      r = this.s < 0 ? n - 1 : 0;
  if (this.t > 0) if (d == 0) r = this[0] % n;else for (var i = this.t - 1; i >= 0; --i) {
    r = (d * r + this[i]) % n;
  }
  return r;
} // (public) 1/this % m (HAC 14.61)


function bnModInverse(m) {
  var ac = m.isEven();
  if (this.isEven() && ac || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(),
      v = this.clone();
  var a = nbv(1),
      b = nbv(0),
      c = nbv(0),
      d = nbv(1);

  while (u.signum() != 0) {
    while (u.isEven()) {
      u.rShiftTo(1, u);

      if (ac) {
        if (!a.isEven() || !b.isEven()) {
          a.addTo(this, a);
          b.subTo(m, b);
        }

        a.rShiftTo(1, a);
      } else if (!b.isEven()) b.subTo(m, b);

      b.rShiftTo(1, b);
    }

    while (v.isEven()) {
      v.rShiftTo(1, v);

      if (ac) {
        if (!c.isEven() || !d.isEven()) {
          c.addTo(this, c);
          d.subTo(m, d);
        }

        c.rShiftTo(1, c);
      } else if (!d.isEven()) d.subTo(m, d);

      d.rShiftTo(1, d);
    }

    if (u.compareTo(v) >= 0) {
      u.subTo(v, u);
      if (ac) a.subTo(c, a);
      b.subTo(d, b);
    } else {
      v.subTo(u, v);
      if (ac) c.subTo(a, c);
      d.subTo(b, d);
    }
  }

  if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if (d.compareTo(m) >= 0) return d.subtract(m);
  if (d.signum() < 0) d.addTo(m, d);else return d;
  if (d.signum() < 0) return d.add(m);else return d;
}

var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
var lplim = (1 << 26) / lowprimes[lowprimes.length - 1]; // (public) test primality with certainty >= 1-.5^t

function bnIsProbablePrime(t) {
  var i,
      x = this.abs();

  if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
    for (i = 0; i < lowprimes.length; ++i) {
      if (x[0] == lowprimes[i]) return true;
    }

    return false;
  }

  if (x.isEven()) return false;
  i = 1;

  while (i < lowprimes.length) {
    var m = lowprimes[i],
        j = i + 1;

    while (j < lowprimes.length && m < lplim) {
      m *= lowprimes[j++];
    }

    m = x.modInt(m);

    while (i < j) {
      if (m % lowprimes[i++] == 0) return false;
    }
  }

  return x.millerRabin(t);
} // (protected) true if probably prime (HAC 4.24, Miller-Rabin)


function bnpMillerRabin(t) {
  var n1 = this.subtract(BigInteger.ONE);
  var k = n1.getLowestSetBit();
  if (k <= 0) return false;
  var r = n1.shiftRight(k);
  t = t + 1 >> 1;
  if (t > lowprimes.length) t = lowprimes.length;
  var a = nbi();

  for (var i = 0; i < t; ++i) {
    //Pick bases at random, instead of starting at 2
    a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
    var y = a.modPow(r, this);

    if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
      var j = 1;

      while (j++ < k && y.compareTo(n1) != 0) {
        y = y.modPowInt(2, this);
        if (y.compareTo(BigInteger.ONE) == 0) return false;
      }

      if (y.compareTo(n1) != 0) return false;
    }
  }

  return true;
} // protected


BigInteger.prototype.chunkSize = bnpChunkSize;
BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.fromRadix = bnpFromRadix;
BigInteger.prototype.fromNumber = bnpFromNumber;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
BigInteger.prototype.changeBit = bnpChangeBit;
BigInteger.prototype.addTo = bnpAddTo;
BigInteger.prototype.dMultiply = bnpDMultiply;
BigInteger.prototype.dAddOffset = bnpDAddOffset;
BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
BigInteger.prototype.modInt = bnpModInt;
BigInteger.prototype.millerRabin = bnpMillerRabin; // public

BigInteger.prototype.clone = bnClone;
BigInteger.prototype.intValue = bnIntValue;
BigInteger.prototype.byteValue = bnByteValue;
BigInteger.prototype.shortValue = bnShortValue;
BigInteger.prototype.signum = bnSigNum;
BigInteger.prototype.toByteArray = bnToByteArray;
BigInteger.prototype.equals = bnEquals;
BigInteger.prototype.min = bnMin;
BigInteger.prototype.max = bnMax;
BigInteger.prototype.and = bnAnd;
BigInteger.prototype.or = bnOr;
BigInteger.prototype.xor = bnXor;
BigInteger.prototype.andNot = bnAndNot;
BigInteger.prototype.not = bnNot;
BigInteger.prototype.shiftLeft = bnShiftLeft;
BigInteger.prototype.shiftRight = bnShiftRight;
BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
BigInteger.prototype.bitCount = bnBitCount;
BigInteger.prototype.testBit = bnTestBit;
BigInteger.prototype.setBit = bnSetBit;
BigInteger.prototype.clearBit = bnClearBit;
BigInteger.prototype.flipBit = bnFlipBit;
BigInteger.prototype.add = bnAdd;
BigInteger.prototype.subtract = bnSubtract;
BigInteger.prototype.multiply = bnMultiply;
BigInteger.prototype.divide = bnDivide;
BigInteger.prototype.remainder = bnRemainder;
BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
BigInteger.prototype.modPow = bnModPow;
BigInteger.prototype.modInverse = bnModInverse;
BigInteger.prototype.pow = bnPow;
BigInteger.prototype.gcd = bnGCD;
BigInteger.prototype.isProbablePrime = bnIsProbablePrime; // JSBN-specific extension

BigInteger.prototype.square = bnSquare; // BigInteger interfaces not implemented in jsbn:
// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

/*
*
* ec
*
*
* */

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Basic Javascript Elliptic Curve implementation
// Ported loosely from BouncyCastle's Java EC code
// Only Fp curves implemented for now
// Requires jsbn.js and jsbn2.js
// ----------------
// ECFieldElementFp
// constructor

function ECFieldElementFp(q, x) {
  this.x = x; // TODO if(x.compareTo(q) >= 0) error

  this.q = q;
}

function feFpEquals(other) {
  if (other == this) return true;
  return this.q.equals(other.q) && this.x.equals(other.x);
}

function feFpToBigInteger() {
  return this.x;
}

function feFpNegate() {
  return new ECFieldElementFp(this.q, this.x.negate().mod(this.q));
}

function feFpAdd(b) {
  return new ECFieldElementFp(this.q, this.x.add(b.toBigInteger()).mod(this.q));
}

function feFpSubtract(b) {
  return new ECFieldElementFp(this.q, this.x.subtract(b.toBigInteger()).mod(this.q));
}

function feFpMultiply(b) {
  return new ECFieldElementFp(this.q, this.x.multiply(b.toBigInteger()).mod(this.q));
}

function feFpSquare() {
  return new ECFieldElementFp(this.q, this.x.square().mod(this.q));
}

function feFpDivide(b) {
  return new ECFieldElementFp(this.q, this.x.multiply(b.toBigInteger().modInverse(this.q)).mod(this.q));
}

ECFieldElementFp.prototype.equals = feFpEquals;
ECFieldElementFp.prototype.toBigInteger = feFpToBigInteger;
ECFieldElementFp.prototype.negate = feFpNegate;
ECFieldElementFp.prototype.add = feFpAdd;
ECFieldElementFp.prototype.subtract = feFpSubtract;
ECFieldElementFp.prototype.multiply = feFpMultiply;
ECFieldElementFp.prototype.square = feFpSquare;
ECFieldElementFp.prototype.divide = feFpDivide; // ----------------
// ECPointFp
// constructor

function ECPointFp(curve, x, y, z) {
  this.curve = curve;
  this.x = x;
  this.y = y; // Projective coordinates: either zinv == null or z * zinv == 1
  // z and zinv are just BigIntegers, not fieldElements

  if (z == null) {
    this.z = BigInteger.ONE;
  } else {
    this.z = z;
  }

  this.zinv = null; //TODO: compression flag
}

function pointFpGetX() {
  if (this.zinv == null) {
    this.zinv = this.z.modInverse(this.curve.q);
  }

  return this.curve.fromBigInteger(this.x.toBigInteger().multiply(this.zinv).mod(this.curve.q));
}

function pointFpGetY() {
  if (this.zinv == null) {
    this.zinv = this.z.modInverse(this.curve.q);
  }

  return this.curve.fromBigInteger(this.y.toBigInteger().multiply(this.zinv).mod(this.curve.q));
}

function pointFpEquals(other) {
  if (other == this) return true;
  if (this.isInfinity()) return other.isInfinity();
  if (other.isInfinity()) return this.isInfinity();
  var u, v; // u = Y2 * Z1 - Y1 * Z2

  u = other.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(other.z)).mod(this.curve.q);
  if (!u.equals(BigInteger.ZERO)) return false; // v = X2 * Z1 - X1 * Z2

  v = other.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(other.z)).mod(this.curve.q);
  return v.equals(BigInteger.ZERO);
}

function pointFpIsInfinity() {
  if (this.x == null && this.y == null) return true;
  return this.z.equals(BigInteger.ZERO) && !this.y.toBigInteger().equals(BigInteger.ZERO);
}

function pointFpNegate() {
  return new ECPointFp(this.curve, this.x, this.y.negate(), this.z);
}

function pointFpAdd(b) {
  if (this.isInfinity()) return b;
  if (b.isInfinity()) return this; // u = Y2 * Z1 - Y1 * Z2

  var u = b.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(b.z)).mod(this.curve.q); // v = X2 * Z1 - X1 * Z2

  var v = b.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(b.z)).mod(this.curve.q);

  if (BigInteger.ZERO.equals(v)) {
    if (BigInteger.ZERO.equals(u)) {
      return this.twice(); // this == b, so double
    }

    return this.curve.getInfinity(); // this = -b, so infinity
  }

  var THREE = new BigInteger("3");
  var x1 = this.x.toBigInteger();
  var y1 = this.y.toBigInteger();
  var x2 = b.x.toBigInteger();
  var y2 = b.y.toBigInteger();
  var v2 = v.square();
  var v3 = v2.multiply(v);
  var x1v2 = x1.multiply(v2);
  var zu2 = u.square().multiply(this.z); // x3 = v * (z2 * (z1 * u^2 - 2 * x1 * v^2) - v^3)

  var x3 = zu2.subtract(x1v2.shiftLeft(1)).multiply(b.z).subtract(v3).multiply(v).mod(this.curve.q); // y3 = z2 * (3 * x1 * u * v^2 - y1 * v^3 - z1 * u^3) + u * v^3

  var y3 = x1v2.multiply(THREE).multiply(u).subtract(y1.multiply(v3)).subtract(zu2.multiply(u)).multiply(b.z).add(u.multiply(v3)).mod(this.curve.q); // z3 = v^3 * z1 * z2

  var z3 = v3.multiply(this.z).multiply(b.z).mod(this.curve.q);
  return new ECPointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
}

function pointFpTwice() {
  if (this.isInfinity()) return this;
  if (this.y.toBigInteger().signum() == 0) return this.curve.getInfinity(); // TODO: optimized handling of constants

  var THREE = new BigInteger("3");
  var x1 = this.x.toBigInteger();
  var y1 = this.y.toBigInteger();
  var y1z1 = y1.multiply(this.z);
  var y1sqz1 = y1z1.multiply(y1).mod(this.curve.q);
  var a = this.curve.a.toBigInteger(); // w = 3 * x1^2 + a * z1^2

  var w = x1.square().multiply(THREE);

  if (!BigInteger.ZERO.equals(a)) {
    w = w.add(this.z.square().multiply(a));
  }

  w = w.mod(this.curve.q); // x3 = 2 * y1 * z1 * (w^2 - 8 * x1 * y1^2 * z1)

  var x3 = w.square().subtract(x1.shiftLeft(3).multiply(y1sqz1)).shiftLeft(1).multiply(y1z1).mod(this.curve.q); // y3 = 4 * y1^2 * z1 * (3 * w * x1 - 2 * y1^2 * z1) - w^3

  var y3 = w.multiply(THREE).multiply(x1).subtract(y1sqz1.shiftLeft(1)).shiftLeft(2).multiply(y1sqz1).subtract(w.square().multiply(w)).mod(this.curve.q); // z3 = 8 * (y1 * z1)^3

  var z3 = y1z1.square().multiply(y1z1).shiftLeft(3).mod(this.curve.q);
  return new ECPointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
} // Simple NAF (Non-Adjacent Form) multiplication algorithm
// TODO: modularize the multiplication algorithm


function pointFpMultiply(k) {
  if (this.isInfinity()) return this;
  if (k.signum() == 0) return this.curve.getInfinity();
  var e = k;
  var h = e.multiply(new BigInteger("3"));
  var neg = this.negate();
  var R = this;
  var i;

  for (i = h.bitLength() - 2; i > 0; --i) {
    R = R.twice();
    var hBit = h.testBit(i);
    var eBit = e.testBit(i);

    if (hBit != eBit) {
      R = R.add(hBit ? this : neg);
    }
  }

  return R;
} // Compute this*j + x*k (simultaneous multiplication)


function pointFpMultiplyTwo(j, x, k) {
  var i;
  if (j.bitLength() > k.bitLength()) i = j.bitLength() - 1;else i = k.bitLength() - 1;
  var R = this.curve.getInfinity();
  var both = this.add(x);

  while (i >= 0) {
    R = R.twice();

    if (j.testBit(i)) {
      if (k.testBit(i)) {
        R = R.add(both);
      } else {
        R = R.add(this);
      }
    } else {
      if (k.testBit(i)) {
        R = R.add(x);
      }
    }

    --i;
  }

  return R;
}

ECPointFp.prototype.getX = pointFpGetX;
ECPointFp.prototype.getY = pointFpGetY;
ECPointFp.prototype.equals = pointFpEquals;
ECPointFp.prototype.isInfinity = pointFpIsInfinity;
ECPointFp.prototype.negate = pointFpNegate;
ECPointFp.prototype.add = pointFpAdd;
ECPointFp.prototype.twice = pointFpTwice;
ECPointFp.prototype.multiply = pointFpMultiply;
ECPointFp.prototype.multiplyTwo = pointFpMultiplyTwo; // ----------------
// ECCurveFp
// constructor

function ECCurveFp(q, a, b) {
  this.q = q;
  this.a = this.fromBigInteger(a);
  this.b = this.fromBigInteger(b);
  this.infinity = new ECPointFp(this, null, null);
}

function curveFpGetQ() {
  return this.q;
}

function curveFpGetA() {
  return this.a;
}

function curveFpGetB() {
  return this.b;
}

function curveFpEquals(other) {
  if (other == this) return true;
  return this.q.equals(other.q) && this.a.equals(other.a) && this.b.equals(other.b);
}

function curveFpGetInfinity() {
  return this.infinity;
}

function curveFpFromBigInteger(x) {
  return new ECFieldElementFp(this.q, x);
} // for now, work with hex strings because they're easier in JS


function curveFpDecodePointHex(s) {
  switch (parseInt(s.substr(0, 2), 16)) {
    // first byte
    case 0:
      return this.infinity;

    case 2:
    case 3:
      // point compression not supported yet
      return null;

    case 4:
    case 6:
    case 7:
      var len = (s.length - 2) / 2;
      var xHex = s.substr(2, len);
      var yHex = s.substr(len + 2, len);
      return new ECPointFp(this, this.fromBigInteger(new BigInteger(xHex, 16)), this.fromBigInteger(new BigInteger(yHex, 16)));

    default:
      // unsupported
      return null;
  }
}

ECCurveFp.prototype.getQ = curveFpGetQ;
ECCurveFp.prototype.getA = curveFpGetA;
ECCurveFp.prototype.getB = curveFpGetB;
ECCurveFp.prototype.equals = curveFpEquals;
ECCurveFp.prototype.getInfinity = curveFpGetInfinity;
ECCurveFp.prototype.fromBigInteger = curveFpFromBigInteger;
ECCurveFp.prototype.decodePointHex = curveFpDecodePointHex;
/*
*
* ecparam-1.0
*
*
*
* */

/*! ecparam-1.0.0.js (c) 2013 Kenji Urushima | kjur.github.com/jsrsasign/license
 */

/*
 * ecparam.js - Elliptic Curve Cryptography Curve Parameter Definition class
 *
 * Copyright (c) 2013 Kenji Urushima (kenji.urushima@gmail.com)
 *
 * This software is licensed under the terms of the MIT License.
 * http://kjur.github.com/jsrsasign/license
 *
 * The above copyright and license notice shall be
 * included in all copies or substantial portions of the Software.
 */

/**
 * @fileOverview
 * @name ecparam-1.1.js
 * @author Kenji Urushima kenji.urushima@gmail.com
 * @version 1.0.0 (2013-Jul-17)
 * @since jsrsasign 4.0
 * @license <a href="http://kjur.github.io/jsrsasign/license/">MIT License</a>
 */

var KJUR = KJUR ? KJUR : {}; // if (typeof KJUR == "undefined" || !KJUR) KJUR = {};

if (typeof KJUR.crypto == "undefined" || !KJUR.crypto) KJUR.crypto = {};
/**
 * static object for elliptic curve names and parameters
 * @name KJUR.crypto.ECParameterDB
 * @class static object for elliptic curve names and parameters
 * @description
 * This class provides parameters for named elliptic curves.
 * Currently it supoprts following curve names and aliases however
 * the name marked (*) are available for {@link KJUR.crypto.ECDSA} and
 * {@link KJUR.crypto.Signature} classes.
 * <ul>
 * <li>secp128r1</li>
 * <li>secp160r1</li>
 * <li>secp160k1</li>
 * <li>secp192r1</li>
 * <li>secp192k1</li>
 * <li>secp224r1</li>
 * <li>secp256r1, NIST P-256, P-256, prime256v1 (*)</li>
 * <li>secp256k1 (*)</li>
 * <li>secp384r1, NIST P-384, P-384 (*)</li>
 * <li>secp521r1, NIST P-521, P-521</li>
 * </ul>
 * You can register new curves by using 'register' method.
 */

KJUR.crypto.ECParameterDB = new function () {
  var db = {};
  var aliasDB = {};

  function hex2bi(hex) {
    return new BigInteger(hex, 16);
  }
  /**
   * get curve inforamtion associative array for curve name or alias
   * @name getByName
   * @memberOf KJUR.crypto.ECParameterDB
   * @function
   * @param {String} nameOrAlias curve name or alias name
   * @return {Array} associative array of curve parameters
   * @example
   * var param = KJUR.crypto.ECParameterDB.getByName('prime256v1');
   * var keylen = param['keylen'];
   * var n = param['n'];
   */


  this.getByName = function (nameOrAlias) {
    var name = nameOrAlias;

    if (typeof aliasDB[name] != "undefined") {
      name = aliasDB[nameOrAlias];
    }

    if (typeof db[name] != "undefined") {
      return db[name];
    }

    throw "unregistered EC curve name: " + name;
  };
  /**
   * register new curve
   * @name regist
   * @memberOf KJUR.crypto.ECParameterDB
   * @function
   * @param {String} name name of curve
   * @param {Integer} keylen key length
   * @param {String} pHex hexadecimal value of p
   * @param {String} aHex hexadecimal value of a
   * @param {String} bHex hexadecimal value of b
   * @param {String} nHex hexadecimal value of n
   * @param {String} hHex hexadecimal value of h
   * @param {String} gxHex hexadecimal value of Gx
   * @param {String} gyHex hexadecimal value of Gy
   * @param {Array} aliasList array of string for curve names aliases
   * @param {String} oid Object Identifier for the curve
   * @param {String} info information string for the curve
   */


  this.regist = function (name, keylen, pHex, aHex, bHex, nHex, hHex, gxHex, gyHex, aliasList, oid, info) {
    db[name] = {};
    var p = hex2bi(pHex);
    var a = hex2bi(aHex);
    var b = hex2bi(bHex);
    var n = hex2bi(nHex);
    var h = hex2bi(hHex);
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04" + gxHex + gyHex);
    db[name]['name'] = name;
    db[name]['keylen'] = keylen;
    db[name]['curve'] = curve;
    db[name]['G'] = G;
    db[name]['n'] = n;
    db[name]['h'] = h;
    db[name]['oid'] = oid;
    db[name]['info'] = info;

    for (var i = 0; i < aliasList.length; i++) {
      aliasDB[aliasList[i]] = name;
    }
  };
}();
KJUR.crypto.ECParameterDB.regist("secp128r1", // name / p = 2^128 - 2^97 - 1
128, "FFFFFFFDFFFFFFFFFFFFFFFFFFFFFFFF", // p
"FFFFFFFDFFFFFFFFFFFFFFFFFFFFFFFC", // a
"E87579C11079F43DD824993C2CEE5ED3", // b
"FFFFFFFE0000000075A30D1B9038A115", // n
"1", // h
"161FF7528B899B2D0C28607CA52C5B86", // gx
"CF5AC8395BAFEB13C02DA292DDED7A83", // gy
[], // alias
"", // oid (underconstruction)
"secp128r1 : SECG curve over a 128 bit prime field"); // info

KJUR.crypto.ECParameterDB.regist("secp160k1", // name / p = 2^160 - 2^32 - 2^14 - 2^12 - 2^9 - 2^8 - 2^7 - 2^3 - 2^2 - 1
160, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFAC73", // p
"0", // a
"7", // b
"0100000000000000000001B8FA16DFAB9ACA16B6B3", // n
"1", // h
"3B4C382CE37AA192A4019E763036F4F5DD4D7EBB", // gx
"938CF935318FDCED6BC28286531733C3F03C4FEE", // gy
[], // alias
"", // oid
"secp160k1 : SECG curve over a 160 bit prime field"); // info

KJUR.crypto.ECParameterDB.regist("secp160r1", // name / p = 2^160 - 2^31 - 1
160, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7FFFFFFF", // p
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7FFFFFFC", // a
"1C97BEFC54BD7A8B65ACF89F81D4D4ADC565FA45", // b
"0100000000000000000001F4C8F927AED3CA752257", // n
"1", // h
"4A96B5688EF573284664698968C38BB913CBFC82", // gx
"23A628553168947D59DCC912042351377AC5FB32", // gy
[], // alias
"", // oid
"secp160r1 : SECG curve over a 160 bit prime field"); // info

KJUR.crypto.ECParameterDB.regist("secp192k1", // name / p = 2^192 - 2^32 - 2^12 - 2^8 - 2^7 - 2^6 - 2^3 - 1
192, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFEE37", // p
"0", // a
"3", // b
"FFFFFFFFFFFFFFFFFFFFFFFE26F2FC170F69466A74DEFD8D", // n
"1", // h
"DB4FF10EC057E9AE26B07D0280B7F4341DA5D1B1EAE06C7D", // gx
"9B2F2F6D9C5628A7844163D015BE86344082AA88D95E2F9D", // gy
[]); // alias

KJUR.crypto.ECParameterDB.regist("secp192r1", // name / p = 2^192 - 2^64 - 1
192, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF", // p
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFC", // a
"64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1", // b
"FFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831", // n
"1", // h
"188DA80EB03090F67CBF20EB43A18800F4FF0AFD82FF1012", // gx
"07192B95FFC8DA78631011ED6B24CDD573F977A11E794811", // gy
[]); // alias

KJUR.crypto.ECParameterDB.regist("secp224r1", // name / p = 2^224 - 2^96 + 1
224, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001", // p
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFE", // a
"B4050A850C04B3ABF54132565044B0B7D7BFD8BA270B39432355FFB4", // b
"FFFFFFFFFFFFFFFFFFFFFFFFFFFF16A2E0B8F03E13DD29455C5C2A3D", // n
"1", // h
"B70E0CBD6BB4BF7F321390B94A03C1D356C21122343280D6115C1D21", // gx
"BD376388B5F723FB4C22DFE6CD4375A05A07476444D5819985007E34", // gy
[]); // alias

KJUR.crypto.ECParameterDB.regist("secp256k1", // name / p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
256, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", // p
"0", // a
"7", // b
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", // n
"1", // h
"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", // gx
"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", // gy
[]); // alias

KJUR.crypto.ECParameterDB.regist("secp256r1", // name / p = 2^224 (2^32 - 1) + 2^192 + 2^96 - 1
256, "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF", // p
"FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC", // a
"5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B", // b
"FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551", // n
"1", // h
"6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296", // gx
"4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5", // gy
["NIST P-256", "P-256", "prime256v1"]); // alias

KJUR.crypto.ECParameterDB.regist("secp384r1", // name
384, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF", // p
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFC", // a
"B3312FA7E23EE7E4988E056BE3F82D19181D9C6EFE8141120314088F5013875AC656398D8A2ED19D2A85C8EDD3EC2AEF", // b
"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973", // n
"1", // h
"AA87CA22BE8B05378EB1C71EF320AD746E1D3B628BA79B9859F741E082542A385502F25DBF55296C3A545E3872760AB7", // gx
"3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", // gy
["NIST P-384", "P-384"]); // alias

KJUR.crypto.ECParameterDB.regist("secp521r1", // name
521, "1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", // p
"1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC", // a
"051953EB9618E1C9A1F929A21A0B68540EEA2DA725B99B315F3B8B489918EF109E156193951EC7E937B1652C0BD3BB1BF073573DF883D2C34F1EF451FD46B503F00", // b
"1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409", // n
"1", // h
"C6858E06B70404E9CD9E3ECB662395B4429C648139053FB521F828AF606B4D3DBAA14B5E77EFE75928FE1DC127A2FFA8DE3348B3C1856A429BF97E7E31C2E5BD66", // gx
"011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650", // gy
["NIST P-521", "P-521"]); // alias
// SM2正式参数

KJUR.crypto.ECParameterDB.regist("sm2", // name
256, "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF", // p
"FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC", // a
"28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93", // b
"FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123", // n
"1", // h
"32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7", // gx
"BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0", // gy
["SM2"]); // alias
// SM2白皮书测试参数
// KJUR.crypto.ECParameterDB.regist(
//   "sm2", // name
//   256,
//   "8542D69E4C044F18E8B92435BF6FF7DE457283915C45517D722EDB8B08F1DFC3", // p
//   "787968B4FA32C3FD2417842E73BBFEFF2F3C848B6831D7E0EC65228B3937E498", // a
//   "63E4C6D3B23B0C849CF84241484BFE48F61D59A5B16BA06E6E12D1DA27C5249A", // b
//   "8542D69E4C044F18E8B92435BF6FF7DD297720630485628D5AE74EE7C32E79B7", // n
//   "1", // h
//   "421DEBD61B62EAB6746434EBC3CC315E32220B3BADD50BDC4C4E6C147FEDD43D", // gx
//   "0680512BCBB42C07D47349D2153B70C4E5D7FDFCBFA36EA1A85841B9E46E09A2", // gy
//   ["SM2"]); // alias

/*
*
*
* prng4
*
*
* */

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// prng4.js - uses Arcfour as a PRNG

function Arcfour() {
  this.i = 0;
  this.j = 0;
  this.S = new Array();
} // Initialize arcfour context from key, an array of ints, each from [0..255]


function ARC4init(key) {
  var i, j, t;

  for (i = 0; i < 256; ++i) {
    this.S[i] = i;
  }

  j = 0;

  for (i = 0; i < 256; ++i) {
    j = j + this.S[i] + key[i % key.length] & 255;
    t = this.S[i];
    this.S[i] = this.S[j];
    this.S[j] = t;
  }

  this.i = 0;
  this.j = 0;
}

function ARC4next() {
  var t;
  this.i = this.i + 1 & 255;
  this.j = this.j + this.S[this.i] & 255;
  t = this.S[this.i];
  this.S[this.i] = this.S[this.j];
  this.S[this.j] = t;
  return this.S[t + this.S[this.i] & 255];
}

Arcfour.prototype.init = ARC4init;
Arcfour.prototype.next = ARC4next; // Plug in your RNG constructor here

function prng_newstate() {
  return new Arcfour();
} // Pool size must be a multiple of 4 and greater than 32.
// An array of bytes the size of the pool will be passed to init()


var rng_psize = 256;
/**
 *
 *
 *
 *
 *
 *rng
 *
 *
 *
 *
 *
 * */

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Random number generator - requires a PRNG backend, e.g. prng4.js
// For best results, put code like
// <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
// in your main HTML document.

var rng_state;
var rng_pool;
var rng_pptr; // Mix in a 32-bit integer into the pool

function rng_seed_int(x) {
  rng_pool[rng_pptr++] ^= x & 255;
  rng_pool[rng_pptr++] ^= x >> 8 & 255;
  rng_pool[rng_pptr++] ^= x >> 16 & 255;
  rng_pool[rng_pptr++] ^= x >> 24 & 255;
  if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
} // Mix in the current time (w/milliseconds) into the pool


function rng_seed_time() {
  rng_seed_int(new Date().getTime());
} // Initialize the pool with junk if needed.


if (rng_pool == null) {
  rng_pool = new Array();
  rng_pptr = 0;
  var t;

  if (window.crypto && window.crypto.getRandomValues) {
    // Use webcrypto if available
    var ua = new Uint8Array(32);
    window.crypto.getRandomValues(ua);

    for (t = 0; t < 32; ++t) {
      rng_pool[rng_pptr++] = ua[t];
    }
  }

  if (navigator.appName == "Netscape" && navigator.appVersion < "5" && window.crypto) {
    // Extract entropy (256 bits) from NS4 RNG if available
    var z = window.crypto.random(32);

    for (t = 0; t < z.length; ++t) {
      rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
    }
  }

  while (rng_pptr < rng_psize) {
    // extract some randomness from Math.random()
    t = Math.floor(65536 * Math.random());
    rng_pool[rng_pptr++] = t >>> 8;
    rng_pool[rng_pptr++] = t & 255;
  }

  rng_pptr = 0;
  rng_seed_time(); //rng_seed_int(window.screenX);
  //rng_seed_int(window.screenY);
}

function rng_get_byte() {
  if (rng_state == null) {
    rng_seed_time();
    rng_state = prng_newstate();
    rng_state.init(rng_pool);

    for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr) {
      rng_pool[rng_pptr] = 0;
    }

    rng_pptr = 0; //rng_pool = null;
  } // TODO: allow reseeding after first request


  return rng_state.next();
}

function rng_get_bytes(ba) {
  var i;

  for (i = 0; i < ba.length; ++i) {
    ba[i] = rng_get_byte();
  }
}

function SecureRandom() {}

SecureRandom.prototype.nextBytes = rng_get_bytes;
/**
 *
 *
 *
 *
 *
 *
 * ecdsa-modifued
 *
 *
 *
 *
 *
 */

/*! ecdsa-modified-1.1.0.js (c) Stephan Thomas, Kenji Urushima | github.com/bitcoinjs/bitcoinjs-lib/blob/master/LICENSE
 */

/*
 * ecdsa-modified.js - modified Bitcoin.ECDSA class
 *
 * Copyright (c) 2013-2017 Stefan Thomas (github.com/justmoon)
 *                         Kenji Urushima (kenji.urushima@gmail.com)
 * LICENSE
 *   https://github.com/bitcoinjs/bitcoinjs-lib/blob/master/LICENSE
 */

/**
 * @fileOverview
 * @name ecdsa-modified-1.0.js
 * @author Stefan Thomas (github.com/justmoon) and Kenji Urushima (kenji.urushima@gmail.com)
 * @version 1.1.0 (2017-Jan-21)
 * @since jsrsasign 4.0
 * @license <a href="https://github.com/bitcoinjs/bitcoinjs-lib/blob/master/LICENSE">MIT License</a>
 */

if (typeof KJUR == "undefined" || !KJUR) KJUR = {};
if (typeof KJUR.crypto == "undefined" || !KJUR.crypto) KJUR.crypto = {};
/**
 * class for EC key generation,  ECDSA signing and verifcation
 * @name KJUR.crypto.ECDSA
 * @class class for EC key generation,  ECDSA signing and verifcation
 * @description
 * <p>
 * CAUTION: Most of the case, you don't need to use this class except
 * for generating an EC key pair. Please use {@link KJUR.crypto.Signature} class instead.
 * </p>
 * <p>
 * This class was originally developped by Stefan Thomas for Bitcoin JavaScript library.
 * (See {@link https://github.com/bitcoinjs/bitcoinjs-lib/blob/master/src/ecdsa.js})
 * Currently this class supports following named curves and their aliases.
 * <ul>
 * <li>secp256r1, NIST P-256, P-256, prime256v1 (*)</li>
 * <li>secp256k1 (*)</li>
 * <li>secp384r1, NIST P-384, P-384 (*)</li>
 * </ul>
 * </p>
 */

KJUR.crypto.ECDSA = function (params) {
  var curveName = "secp256r1"; // curve name default

  var ecparams = null;
  var prvKeyHex = null;
  var pubKeyHex = null;
  var rng = new SecureRandom();
  var P_OVER_FOUR = null;
  this.type = "EC";
  this.isPrivate = false;
  this.isPublic = false;

  function implShamirsTrick(P, k, Q, l) {
    var m = Math.max(k.bitLength(), l.bitLength());
    var Z = P.add2D(Q);
    var R = P.curve.getInfinity();

    for (var i = m - 1; i >= 0; --i) {
      R = R.twice2D();
      R.z = BigInteger.ONE;

      if (k.testBit(i)) {
        if (l.testBit(i)) {
          R = R.add2D(Z);
        } else {
          R = R.add2D(P);
        }
      } else {
        if (l.testBit(i)) {
          R = R.add2D(Q);
        }
      }
    }

    return R;
  }

  ; //===========================
  // PUBLIC METHODS
  //===========================

  this.getBigRandom = function (limit) {
    return new BigInteger(limit.bitLength(), rng).mod(limit.subtract(BigInteger.ONE)).add(BigInteger.ONE);
  };

  this.setNamedCurve = function (curveName) {
    this.ecparams = KJUR.crypto.ECParameterDB.getByName(curveName);
    this.prvKeyHex = null;
    this.pubKeyHex = null;
    this.curveName = curveName;
  };

  this.setPrivateKeyHex = function (prvKeyHex) {
    this.isPrivate = true;
    this.prvKeyHex = prvKeyHex;
  };

  this.setPublicKeyHex = function (pubKeyHex) {
    this.isPublic = true;
    this.pubKeyHex = pubKeyHex;
  };
  /**
  * get X and Y hexadecimal string value of public key
  * @name getPublicKeyXYHex
  * @memberOf KJUR.crypto.ECDSA#
  * @function
  * @return {Array} associative array of x and y value of public key
  * @since ecdsa-modified 1.0.5 jsrsasign 5.0.14
  * @example
  * ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1', 'pub': pubHex});
  * ec.getPublicKeyXYHex() &rarr; { x: '01bacf...', y: 'c3bc22...' }
  */


  this.getPublicKeyXYHex = function () {
    var h = this.pubKeyHex;
    if (h.substr(0, 2) !== "04") throw "this method supports uncompressed format(04) only";
    var charlen = this.ecparams.keylen / 4;
    if (h.length !== 2 + charlen * 2) throw "malformed public key hex length";
    var result = {};
    result.x = h.substr(2, charlen);
    result.y = h.substr(2 + charlen);
    return result;
  };
  /**
   * get NIST curve short name such as "P-256" or "P-384"
   * @name getShortNISTPCurveName
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @return {String} short NIST P curve name such as "P-256" or "P-384" if it's NIST P curve otherwise null;
   * @since ecdsa-modified 1.0.5 jsrsasign 5.0.14
   * @example
   * ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1', 'pub': pubHex});
   * ec.getShortPCurveName() &rarr; "P-256";
   */


  this.getShortNISTPCurveName = function () {
    var s = this.curveName;
    if (s === "secp256r1" || s === "NIST P-256" || s === "P-256" || s === "prime256v1") return "P-256";
    if (s === "secp384r1" || s === "NIST P-384" || s === "P-384") return "P-384";
    return null;
  };
  /**
   * generate a EC key pair
   * @name generateKeyPairHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @return {Array} associative array of hexadecimal string of private and public key
   * @since ecdsa-modified 1.0.1
   * @example
   * var ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1'});
   * var keypair = ec.generateKeyPairHex();
   * var pubhex = keypair.ecpubhex; // hexadecimal string of EC public key
   * var prvhex = keypair.ecprvhex; // hexadecimal string of EC private key (=d)
   */


  this.generateKeyPairHex = function () {
    var biN = this.ecparams['n'];
    var biPrv = this.getBigRandom(biN);
    var epPub = this.ecparams['G'].multiply(biPrv);
    var biX = epPub.getX().toBigInteger();
    var biY = epPub.getY().toBigInteger();
    var charlen = this.ecparams['keylen'] / 4;
    var hPrv = ("0000000000" + biPrv.toString(16)).slice(-charlen);
    var hX = ("0000000000" + biX.toString(16)).slice(-charlen);
    var hY = ("0000000000" + biY.toString(16)).slice(-charlen);
    var hPub = "04" + hX + hY;
    this.setPrivateKeyHex(hPrv);
    this.setPublicKeyHex(hPub);
    return {
      'ecprvhex': hPrv,
      'ecpubhex': hPub
    };
  };

  this.signWithMessageHash = function (hashHex) {
    return this.signHex(hashHex, this.prvKeyHex);
  };
  /**
   * signing to message hash
   * @name signHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} hashHex hexadecimal string of hash value of signing message
   * @param {String} privHex hexadecimal string of EC private key
   * @return {String} hexadecimal string of ECDSA signature
   * @since ecdsa-modified 1.0.1
   * @example
   * var ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1'});
   * var sigValue = ec.signHex(hash, prvKey);
   */


  this.signHex = function (hashHex, privHex) {
    var d = new BigInteger(privHex, 16);
    var n = this.ecparams['n'];
    var e = new BigInteger(hashHex, 16);

    do {
      var k = this.getBigRandom(n);
      var G = this.ecparams['G'];
      var Q = G.multiply(k);
      var r = Q.getX().toBigInteger().mod(n);
    } while (r.compareTo(BigInteger.ZERO) <= 0);

    var s = k.modInverse(n).multiply(e.add(d.multiply(r))).mod(n);
    return KJUR.crypto.ECDSA.biRSSigToASN1Sig(r, s);
  };

  this.sign = function (hash, priv) {
    var d = priv;
    var n = this.ecparams['n'];
    var e = BigInteger.fromByteArrayUnsigned(hash);

    do {
      var k = this.getBigRandom(n);
      var G = this.ecparams['G'];
      var Q = G.multiply(k);
      var r = Q.getX().toBigInteger().mod(n);
    } while (r.compareTo(BigInteger.ZERO) <= 0);

    var s = k.modInverse(n).multiply(e.add(d.multiply(r))).mod(n);
    return this.serializeSig(r, s);
  };

  this.verifyWithMessageHash = function (hashHex, sigHex) {
    return this.verifyHex(hashHex, sigHex, this.pubKeyHex);
  };
  /**
   * verifying signature with message hash and public key
   * @name verifyHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} hashHex hexadecimal string of hash value of signing message
   * @param {String} sigHex hexadecimal string of signature value
   * @param {String} pubkeyHex hexadecimal string of public key
   * @return {Boolean} true if the signature is valid, otherwise false
   * @since ecdsa-modified 1.0.1
   * @example
   * var ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1'});
   * var result = ec.verifyHex(msgHashHex, sigHex, pubkeyHex);
   */


  this.verifyHex = function (hashHex, sigHex, pubkeyHex) {
    var r, s;
    var obj = KJUR.crypto.ECDSA.parseSigHex(sigHex);
    r = obj.r;
    s = obj.s;
    var Q;
    Q = ECPointFp.decodeFromHex(this.ecparams['curve'], pubkeyHex);
    var e = new BigInteger(hashHex, 16);
    return this.verifyRaw(e, r, s, Q);
  };

  this.verify = function (hash, sig, pubkey) {
    var r, s;

    if (Bitcoin.Util.isArray(sig)) {
      var obj = this.parseSig(sig);
      r = obj.r;
      s = obj.s;
    } else if ("object" === _typeof(sig) && sig.r && sig.s) {
      r = sig.r;
      s = sig.s;
    } else {
      throw "Invalid value for signature";
    }

    var Q;

    if (pubkey instanceof ECPointFp) {
      Q = pubkey;
    } else if (Bitcoin.Util.isArray(pubkey)) {
      Q = ECPointFp.decodeFrom(this.ecparams['curve'], pubkey);
    } else {
      throw "Invalid format for pubkey value, must be byte array or ECPointFp";
    }

    var e = BigInteger.fromByteArrayUnsigned(hash);
    return this.verifyRaw(e, r, s, Q);
  };

  this.verifyRaw = function (e, r, s, Q) {
    var n = this.ecparams['n'];
    var G = this.ecparams['G'];
    if (r.compareTo(BigInteger.ONE) < 0 || r.compareTo(n) >= 0) return false;
    if (s.compareTo(BigInteger.ONE) < 0 || s.compareTo(n) >= 0) return false;
    var c = s.modInverse(n);
    var u1 = e.multiply(c).mod(n);
    var u2 = r.multiply(c).mod(n); // TODO(!!!): For some reason Shamir's trick isn't working with
    // signed message verification!? Probably an implementation
    // error!
    //var point = implShamirsTrick(G, u1, Q, u2);

    var point = G.multiply(u1).add(Q.multiply(u2));
    var v = point.getX().toBigInteger().mod(n);
    return v.equals(r);
  };
  /**
   * Serialize a signature into DER format.
   *
   * Takes two BigIntegers representing r and s and returns a byte array.
   */


  this.serializeSig = function (r, s) {
    var rBa = r.toByteArraySigned();
    var sBa = s.toByteArraySigned();
    var sequence = [];
    sequence.push(0x02); // INTEGER

    sequence.push(rBa.length);
    sequence = sequence.concat(rBa);
    sequence.push(0x02); // INTEGER

    sequence.push(sBa.length);
    sequence = sequence.concat(sBa);
    sequence.unshift(sequence.length);
    sequence.unshift(0x30); // SEQUENCE

    return sequence;
  };
  /**
   * Parses a byte array containing a DER-encoded signature.
   *
   * This function will return an object of the form:
   *
   * {
     *   r: BigInteger,
     *   s: BigInteger
     * }
   */


  this.parseSig = function (sig) {
    var cursor;
    if (sig[0] != 0x30) throw new Error("Signature not a valid DERSequence");
    cursor = 2;
    if (sig[cursor] != 0x02) throw new Error("First element in signature must be a DERInteger");
    ;
    var rBa = sig.slice(cursor + 2, cursor + 2 + sig[cursor + 1]);
    cursor += 2 + sig[cursor + 1];
    if (sig[cursor] != 0x02) throw new Error("Second element in signature must be a DERInteger");
    var sBa = sig.slice(cursor + 2, cursor + 2 + sig[cursor + 1]);
    cursor += 2 + sig[cursor + 1]; //if (cursor != sig.length)
    //  throw new Error("Extra bytes in signature");

    var r = BigInteger.fromByteArrayUnsigned(rBa);
    var s = BigInteger.fromByteArrayUnsigned(sBa);
    return {
      r: r,
      s: s
    };
  };

  this.parseSigCompact = function (sig) {
    if (sig.length !== 65) {
      throw "Signature has the wrong length";
    } // Signature is prefixed with a type byte storing three bits of
    // information.


    var i = sig[0] - 27;

    if (i < 0 || i > 7) {
      throw "Invalid signature type";
    }

    var n = this.ecparams['n'];
    var r = BigInteger.fromByteArrayUnsigned(sig.slice(1, 33)).mod(n);
    var s = BigInteger.fromByteArrayUnsigned(sig.slice(33, 65)).mod(n);
    return {
      r: r,
      s: s,
      i: i
    };
  };
  /**
   * read an ASN.1 hexadecimal string of PKCS#1/5 plain ECC private key<br/>
   * @name readPKCS5PrvKeyHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} h hexadecimal string of PKCS#1/5 ECC private key
   * @since jsrsasign 7.1.0 ecdsa-modified 1.1.0
   */


  this.readPKCS5PrvKeyHex = function (h) {
    var _ASN1HEX = ASN1HEX;
    var _getName = KJUR.crypto.ECDSA.getName;
    var _getVbyList = _ASN1HEX.getVbyList;
    if (_ASN1HEX.isASN1HEX(h) === false) throw "not ASN.1 hex string";
    var hCurve, hPrv, hPub;

    try {
      hCurve = _getVbyList(h, 0, [2, 0], "06");
      hPrv = _getVbyList(h, 0, [1], "04");

      try {
        hPub = _getVbyList(h, 0, [3, 0], "03").substr(2);
      } catch (ex) {}

      ;
    } catch (ex) {
      throw "malformed PKCS#1/5 plain ECC private key";
    }

    this.curveName = _getName(hCurve);
    if (this.curveName === undefined) throw "unsupported curve name";
    this.setNamedCurve(this.curveName);
    this.setPublicKeyHex(hPub);
    this.setPrivateKeyHex(hPrv);
    this.isPublic = false;
  };
  /**
   * read an ASN.1 hexadecimal string of PKCS#8 plain ECC private key<br/>
   * @name readPKCS8PrvKeyHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} h hexadecimal string of PKCS#8 ECC private key
   * @since jsrsasign 7.1.0 ecdsa-modified 1.1.0
   */


  this.readPKCS8PrvKeyHex = function (h) {
    var _ASN1HEX = ASN1HEX;
    var _getName = KJUR.crypto.ECDSA.getName;
    var _getVbyList = _ASN1HEX.getVbyList;
    if (_ASN1HEX.isASN1HEX(h) === false) throw "not ASN.1 hex string";
    var hECOID, hCurve, hPrv, hPub;

    try {
      hECOID = _getVbyList(h, 0, [1, 0], "06");
      hCurve = _getVbyList(h, 0, [1, 1], "06");
      hPrv = _getVbyList(h, 0, [2, 0, 1], "04");

      try {
        hPub = _getVbyList(h, 0, [2, 0, 2, 0], "03").substr(2);
      } catch (ex) {}

      ;
    } catch (ex) {
      throw "malformed PKCS#8 plain ECC private key";
    }

    this.curveName = _getName(hCurve);
    if (this.curveName === undefined) throw "unsupported curve name";
    this.setNamedCurve(this.curveName);
    this.setPublicKeyHex(hPub);
    this.setPrivateKeyHex(hPrv);
    this.isPublic = false;
  };
  /**
   * read an ASN.1 hexadecimal string of PKCS#8 ECC public key<br/>
   * @name readPKCS8PubKeyHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} h hexadecimal string of PKCS#8 ECC public key
   * @since jsrsasign 7.1.0 ecdsa-modified 1.1.0
   */


  this.readPKCS8PubKeyHex = function (h) {
    var _ASN1HEX = ASN1HEX;
    var _getName = KJUR.crypto.ECDSA.getName;
    var _getVbyList = _ASN1HEX.getVbyList;
    if (_ASN1HEX.isASN1HEX(h) === false) throw "not ASN.1 hex string";
    var hECOID, hCurve, hPub;

    try {
      hECOID = _getVbyList(h, 0, [0, 0], "06");
      hCurve = _getVbyList(h, 0, [0, 1], "06");
      hPub = _getVbyList(h, 0, [1], "03").substr(2);
    } catch (ex) {
      throw "malformed PKCS#8 ECC public key";
    }

    this.curveName = _getName(hCurve);
    if (this.curveName === null) throw "unsupported curve name";
    this.setNamedCurve(this.curveName);
    this.setPublicKeyHex(hPub);
  };
  /**
   * read an ASN.1 hexadecimal string of X.509 ECC public key certificate<br/>
   * @name readCertPubKeyHex
   * @memberOf KJUR.crypto.ECDSA#
   * @function
   * @param {String} h hexadecimal string of X.509 ECC public key certificate
   * @param {Integer} nthPKI nth index of publicKeyInfo. (DEFAULT: 6 for X509v3)
   * @since jsrsasign 7.1.0 ecdsa-modified 1.1.0
   */


  this.readCertPubKeyHex = function (h, nthPKI) {
    if (nthPKI !== 5) nthPKI = 6;
    var _ASN1HEX = ASN1HEX;
    var _getName = KJUR.crypto.ECDSA.getName;
    var _getVbyList = _ASN1HEX.getVbyList;
    if (_ASN1HEX.isASN1HEX(h) === false) throw "not ASN.1 hex string";
    var hCurve, hPub;

    try {
      hCurve = _getVbyList(h, 0, [0, nthPKI, 0, 1], "06");
      hPub = _getVbyList(h, 0, [0, nthPKI, 1], "03").substr(2);
    } catch (ex) {
      throw "malformed X.509 certificate ECC public key";
    }

    this.curveName = _getName(hCurve);
    if (this.curveName === null) throw "unsupported curve name";
    this.setNamedCurve(this.curveName);
    this.setPublicKeyHex(hPub);
  };
  /*
   * Recover a public key from a signature.
   *
   * See SEC 1: Elliptic Curve Cryptography, section 4.1.6, "Public
   * Key Recovery Operation".
   *
   * http://www.secg.org/download/aid-780/sec1-v2.pdf
   */

  /*
  recoverPubKey: function (r, s, hash, i) {
  // The recovery parameter i has two bits.
  i = i & 3;
  // The less significant bit specifies whether the y coordinate
  // of the compressed point is even or not.
  var isYEven = i & 1;
  // The more significant bit specifies whether we should use the
  // first or second candidate key.
  var isSecondKey = i >> 1;
  var n = this.ecparams['n'];
  var G = this.ecparams['G'];
  var curve = this.ecparams['curve'];
  var p = curve.getQ();
  var a = curve.getA().toBigInteger();
  var b = curve.getB().toBigInteger();
  // We precalculate (p + 1) / 4 where p is if the field order
  if (!P_OVER_FOUR) {
    P_OVER_FOUR = p.add(BigInteger.ONE).divide(BigInteger.valueOf(4));
  }
  // 1.1 Compute x
  var x = isSecondKey ? r.add(n) : r;
  // 1.3 Convert x to point
  var alpha = x.multiply(x).multiply(x).add(a.multiply(x)).add(b).mod(p);
  var beta = alpha.modPow(P_OVER_FOUR, p);
  var xorOdd = beta.isEven() ? (i % 2) : ((i+1) % 2);
  // If beta is even, but y isn't or vice versa, then convert it,
  // otherwise we're done and y == beta.
  var y = (beta.isEven() ? !isYEven : isYEven) ? beta : p.subtract(beta);
  // 1.4 Check that nR is at infinity
  var R = new ECPointFp(curve,
          curve.fromBigInteger(x),
          curve.fromBigInteger(y));
  R.validate();
  // 1.5 Compute e from M
  var e = BigInteger.fromByteArrayUnsigned(hash);
  var eNeg = BigInteger.ZERO.subtract(e).mod(n);
  // 1.6 Compute Q = r^-1 (sR - eG)
  var rInv = r.modInverse(n);
  var Q = implShamirsTrick(R, s, G, eNeg).multiply(rInv);
  Q.validate();
  if (!this.verifyRaw(e, r, s, Q)) {
    throw "Pubkey recovery unsuccessful";
  }
  var pubKey = new Bitcoin.ECKey();
  pubKey.pub = Q;
  return pubKey;
  },
  */

  /*
   * Calculate pubkey extraction parameter.
   *
   * When extracting a pubkey from a signature, we have to
   * distinguish four different cases. Rather than putting this
   * burden on the verifier, Bitcoin includes a 2-bit value with the
   * signature.
   *
   * This function simply tries all four cases and returns the value
   * that resulted in a successful pubkey recovery.
   */

  /*
  calcPubkeyRecoveryParam: function (address, r, s, hash) {
  for (var i = 0; i < 4; i++) {
    try {
  var pubkey = Bitcoin.ECDSA.recoverPubKey(r, s, hash, i);
  if (pubkey.getBitcoinAddress().toString() == address) {
      return i;
  }
    } catch (e) {}
  }
  throw "Unable to find valid recovery factor";
  }
  */


  if (params !== undefined) {
    if (params['curve'] !== undefined) {
      this.curveName = params['curve'];
    }
  }

  if (this.curveName === undefined) this.curveName = curveName;
  this.setNamedCurve(this.curveName);

  if (params !== undefined) {
    if (params.prv !== undefined) this.setPrivateKeyHex(params.prv);
    if (params.pub !== undefined) this.setPublicKeyHex(params.pub);
  }
};
/**
 * parse ASN.1 DER encoded ECDSA signature
 * @name parseSigHex
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} sigHex hexadecimal string of ECDSA signature value
 * @return {Array} associative array of signature field r and s of BigInteger
 * @since ecdsa-modified 1.0.1
 * @example
 * var ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1'});
 * var sig = ec.parseSigHex('30...');
 * var biR = sig.r; // BigInteger object for 'r' field of signature.
 * var biS = sig.s; // BigInteger object for 's' field of signature.
 */


KJUR.crypto.ECDSA.parseSigHex = function (sigHex) {
  var p = KJUR.crypto.ECDSA.parseSigHexInHexRS(sigHex);
  var biR = new BigInteger(p.r, 16);
  var biS = new BigInteger(p.s, 16);
  return {
    'r': biR,
    's': biS
  };
};
/**
 * parse ASN.1 DER encoded ECDSA signature
 * @name parseSigHexInHexRS
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} sigHex hexadecimal string of ECDSA signature value
 * @return {Array} associative array of signature field r and s in hexadecimal
 * @since ecdsa-modified 1.0.3
 * @example
 * var ec = new KJUR.crypto.ECDSA({'curve': 'secp256r1'});
 * var sig = ec.parseSigHexInHexRS('30...');
 * var hR = sig.r; // hexadecimal string for 'r' field of signature.
 * var hS = sig.s; // hexadecimal string for 's' field of signature.
 */


KJUR.crypto.ECDSA.parseSigHexInHexRS = function (sigHex) {
  // 1. ASN.1 Sequence Check
  if (sigHex.substr(0, 2) != "30") throw "signature is not a ASN.1 sequence"; // 2. Items of ASN.1 Sequence Check

  var a = ASN1HEX.getPosArrayOfChildren_AtObj(sigHex, 0);
  if (a.length != 2) throw "number of signature ASN.1 sequence elements seem wrong"; // 3. Integer check

  var iTLV1 = a[0];
  var iTLV2 = a[1];
  if (sigHex.substr(iTLV1, 2) != "02") throw "1st item of sequene of signature is not ASN.1 integer";
  if (sigHex.substr(iTLV2, 2) != "02") throw "2nd item of sequene of signature is not ASN.1 integer"; // 4. getting value

  var hR = ASN1HEX.getHexOfV_AtObj(sigHex, iTLV1);
  var hS = ASN1HEX.getHexOfV_AtObj(sigHex, iTLV2);
  return {
    'r': hR,
    's': hS
  };
};
/**
 * convert hexadecimal ASN.1 encoded signature to concatinated signature
 * @name asn1SigToConcatSig
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} asn1Hex hexadecimal string of ASN.1 encoded ECDSA signature value
 * @return {String} r-s concatinated format of ECDSA signature value
 * @since ecdsa-modified 1.0.3
 */


KJUR.crypto.ECDSA.asn1SigToConcatSig = function (asn1Sig) {
  var pSig = KJUR.crypto.ECDSA.parseSigHexInHexRS(asn1Sig);
  var hR = pSig.r;
  var hS = pSig.s;
  if (hR.substr(0, 2) == "00" && hR.length / 2 * 8 % (16 * 8) == 8) hR = hR.substr(2);
  if (hS.substr(0, 2) == "00" && hS.length / 2 * 8 % (16 * 8) == 8) hS = hS.substr(2);
  if (hR.length / 2 * 8 % (16 * 8) != 0) throw "unknown ECDSA sig r length error";
  if (hS.length / 2 * 8 % (16 * 8) != 0) throw "unknown ECDSA sig s length error";
  return hR + hS;
};
/**
 * convert hexadecimal concatinated signature to ASN.1 encoded signature
 * @name concatSigToASN1Sig
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} concatSig r-s concatinated format of ECDSA signature value
 * @return {String} hexadecimal string of ASN.1 encoded ECDSA signature value
 * @since ecdsa-modified 1.0.3
 */


KJUR.crypto.ECDSA.concatSigToASN1Sig = function (concatSig) {
  if (concatSig.length / 2 * 8 % (16 * 8) != 0) throw "unknown ECDSA concatinated r-s sig  length error";
  var hR = concatSig.substr(0, concatSig.length / 2);
  var hS = concatSig.substr(concatSig.length / 2);
  return KJUR.crypto.ECDSA.hexRSSigToASN1Sig(hR, hS);
};
/**
 * convert hexadecimal R and S value of signature to ASN.1 encoded signature
 * @name hexRSSigToASN1Sig
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} hR hexadecimal string of R field of ECDSA signature value
 * @param {String} hS hexadecimal string of S field of ECDSA signature value
 * @return {String} hexadecimal string of ASN.1 encoded ECDSA signature value
 * @since ecdsa-modified 1.0.3
 */


KJUR.crypto.ECDSA.hexRSSigToASN1Sig = function (hR, hS) {
  var biR = new BigInteger(hR, 16);
  var biS = new BigInteger(hS, 16);
  return KJUR.crypto.ECDSA.biRSSigToASN1Sig(biR, biS);
};
/**
 * convert R and S BigInteger object of signature to ASN.1 encoded signature
 * @name biRSSigToASN1Sig
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {BigInteger} biR BigInteger object of R field of ECDSA signature value
 * @param {BigInteger} biS BIgInteger object of S field of ECDSA signature value
 * @return {String} hexadecimal string of ASN.1 encoded ECDSA signature value
 * @since ecdsa-modified 1.0.3
 */


KJUR.crypto.ECDSA.biRSSigToASN1Sig = function (biR, biS) {
  var derR = new KJUR.asn1.DERInteger({
    'bigint': biR
  });
  var derS = new KJUR.asn1.DERInteger({
    'bigint': biS
  });
  var derSeq = new KJUR.asn1.DERSequence({
    'array': [derR, derS]
  });
  return derSeq.getEncodedHex();
};
/**
 * static method to get normalized EC curve name from curve name or hexadecimal OID value
 * @name getName
 * @memberOf KJUR.crypto.ECDSA
 * @function
 * @static
 * @param {String} s curve name (ex. P-256) or hexadecimal OID value (ex. 2a86...)
 * @return {String} normalized EC curve name (ex. secp256r1)
 * @since jsrsasign 7.1.0 ecdsa-modified 1.1.0
 * @description
 * This static method returns normalized EC curve name
 * which is supported in jsrsasign
 * from curve name or hexadecimal OID value.
 * When curve is not supported in jsrsasign, this method returns null.
 * Normalized name will be "secp*" in jsrsasign.
 * @example
 * KJUR.crypto.ECDSA.getName("2b8104000a") &rarr; "secp256k1"
 * KJUR.crypto.ECDSA.getName("NIST P-256") &rarr; "secp256r1"
 * KJUR.crypto.ECDSA.getName("P-521") &rarr; undefined // not supported
 */


KJUR.crypto.ECDSA.getName = function (s) {
  if (s === "2a8648ce3d030107") return "secp256r1"; // 1.2.840.10045.3.1.7

  if (s === "2b8104000a") return "secp256k1"; // 1.3.132.0.10

  if (s === "2b81040022") return "secp384r1"; // 1.3.132.0.34

  if ("|secp256r1|NIST P-256|P-256|prime256v1|".indexOf(s) !== -1) return "secp256r1";
  if ("|secp256k1|".indexOf(s) !== -1) return "secp256k1";
  if ("|secp384r1|NIST P-384|P-384|".indexOf(s) !== -1) return "secp384r1";
  return null;
};
/*
*
*
*
*
* ec-patch
*
*
* */

/*! (c) Stefan Thomas | https://github.com/bitcoinjs/bitcoinjs-lib
 */

/*
 * splitted from bitcoin-lib/ecdsa.js
 *
 * version 1.0.0 is the original of bitcoin-lib/ecdsa.js
 */


ECFieldElementFp.prototype.getByteLength = function () {
  return Math.floor((this.toBigInteger().bitLength() + 7) / 8);
};

ECPointFp.prototype.getEncoded = function (compressed) {
  var integerToBytes = function integerToBytes(i, len) {
    var bytes = i.toByteArrayUnsigned();

    if (len < bytes.length) {
      bytes = bytes.slice(bytes.length - len);
    } else while (len > bytes.length) {
      bytes.unshift(0);
    }

    return bytes;
  };

  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger(); // Get value as a 32-byte Buffer
  // Fixed length based on a patch by bitaddress.org and Casascius

  var enc = integerToBytes(x, 32);

  if (compressed) {
    if (y.isEven()) {
      // Compressed even pubkey
      // M = 02 || X
      enc.unshift(0x02);
    } else {
      // Compressed uneven pubkey
      // M = 03 || X
      enc.unshift(0x03);
    }
  } else {
    // Uncompressed pubkey
    // M = 04 || X || Y
    enc.unshift(0x04);
    enc = enc.concat(integerToBytes(y, 32));
  }

  return enc;
};

ECPointFp.decodeFrom = function (curve, enc) {
  var type = enc[0];
  var dataLen = enc.length - 1; // Extract x and y as byte arrays

  var xBa = enc.slice(1, 1 + dataLen / 2);
  var yBa = enc.slice(1 + dataLen / 2, 1 + dataLen); // Prepend zero byte to prevent interpretation as negative integer

  xBa.unshift(0);
  yBa.unshift(0); // Convert to BigIntegers

  var x = new BigInteger(xBa);
  var y = new BigInteger(yBa); // Return point

  return new ECPointFp(curve, curve.fromBigInteger(x), curve.fromBigInteger(y));
};
/*
 * @since ec-patch.js 1.0.1
 */


ECPointFp.decodeFromHex = function (curve, encHex) {
  var type = encHex.substr(0, 2); // shall be "04"

  var dataLen = encHex.length - 2; // Extract x and y as byte arrays

  var xHex = encHex.substr(2, dataLen / 2);
  var yHex = encHex.substr(2 + dataLen / 2, dataLen / 2); // Convert to BigIntegers

  var x = new BigInteger(xHex, 16);
  var y = new BigInteger(yHex, 16); // Return point

  return new ECPointFp(curve, curve.fromBigInteger(x), curve.fromBigInteger(y));
};

ECPointFp.prototype.add2D = function (b) {
  if (this.isInfinity()) return b;
  if (b.isInfinity()) return this;

  if (this.x.equals(b.x)) {
    if (this.y.equals(b.y)) {
      // this = b, i.e. this must be doubled
      return this.twice();
    } // this = -b, i.e. the result is the point at infinity


    return this.curve.getInfinity();
  }

  var x_x = b.x.subtract(this.x);
  var y_y = b.y.subtract(this.y);
  var gamma = y_y.divide(x_x);
  var x3 = gamma.square().subtract(this.x).subtract(b.x);
  var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);
  return new ECPointFp(this.curve, x3, y3);
};

ECPointFp.prototype.twice2D = function () {
  if (this.isInfinity()) return this;

  if (this.y.toBigInteger().signum() == 0) {
    // if y1 == 0, then (x1, y1) == (x1, -y1)
    // and hence this = -this and thus 2(x1, y1) == infinity
    return this.curve.getInfinity();
  }

  var TWO = this.curve.fromBigInteger(BigInteger.valueOf(2));
  var THREE = this.curve.fromBigInteger(BigInteger.valueOf(3));
  var gamma = this.x.square().multiply(THREE).add(this.curve.a).divide(this.y.multiply(TWO));
  var x3 = gamma.square().subtract(this.x.multiply(TWO));
  var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);
  return new ECPointFp(this.curve, x3, y3);
};

ECPointFp.prototype.multiply2D = function (k) {
  if (this.isInfinity()) return this;
  if (k.signum() == 0) return this.curve.getInfinity();
  var e = k;
  var h = e.multiply(new BigInteger("3"));
  var neg = this.negate();
  var R = this;
  var i;

  for (i = h.bitLength() - 2; i > 0; --i) {
    R = R.twice();
    var hBit = h.testBit(i);
    var eBit = e.testBit(i);

    if (hBit != eBit) {
      R = R.add2D(hBit ? this : neg);
    }
  }

  return R;
};

ECPointFp.prototype.isOnCurve = function () {
  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger();
  var a = this.curve.getA().toBigInteger();
  var b = this.curve.getB().toBigInteger();
  var n = this.curve.getQ();
  var lhs = y.multiply(y).mod(n);
  var rhs = x.multiply(x).multiply(x).add(a.multiply(x)).add(b).mod(n);
  return lhs.equals(rhs);
};

ECPointFp.prototype.toString = function () {
  return '(' + this.getX().toBigInteger().toString() + ',' + this.getY().toBigInteger().toString() + ')';
};
/**
 * Validate an elliptic curve point.
 *
 * See SEC 1, section 3.2.2.1: Elliptic Curve Public Key Validation Primitive
 */


ECPointFp.prototype.validate = function () {
  var n = this.curve.getQ(); // Check Q != O

  if (this.isInfinity()) {
    throw new Error("Point is at infinity.");
  } // Check coordinate bounds


  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger();

  if (x.compareTo(BigInteger.ONE) < 0 || x.compareTo(n.subtract(BigInteger.ONE)) > 0) {
    throw new Error('x coordinate out of bounds');
  }

  if (y.compareTo(BigInteger.ONE) < 0 || y.compareTo(n.subtract(BigInteger.ONE)) > 0) {
    throw new Error('y coordinate out of bounds');
  } // Check y^2 = x^3 + ax + b (mod n)


  if (!this.isOnCurve()) {
    throw new Error("Point is not on the curve.");
  } // Check nQ = 0 (Q is a scalar multiple of G)


  if (this.multiply(n).isInfinity()) {
    // TODO: This check doesn't work - fix.
    throw new Error("Point is not a scalar multiple of G.");
  }

  return true;
};
/*
*
*
*
*
* base64
*
*
*
* **/

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */


var b64map = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
var b64pad = "=";

function hex2b64(h) {
  var i;
  var c;
  var ret = "";

  for (i = 0; i + 3 <= h.length; i += 3) {
    c = parseInt(h.substring(i, i + 3), 16);
    ret += b64map.charAt(c >> 6) + b64map.charAt(c & 63);
  }

  if (i + 1 == h.length) {
    c = parseInt(h.substring(i, i + 1), 16);
    ret += b64map.charAt(c << 2);
  } else if (i + 2 == h.length) {
    c = parseInt(h.substring(i, i + 2), 16);
    ret += b64map.charAt(c >> 2) + b64map.charAt((c & 3) << 4);
  }

  if (b64pad) while ((ret.length & 3) > 0) {
    ret += b64pad;
  }
  return ret;
} // convert a base64 string to hex


function b64tohex(s) {
  var ret = "";
  var i;
  var k = 0; // b64 state, 0-3

  var slop;
  var v;

  for (i = 0; i < s.length; ++i) {
    if (s.charAt(i) == b64pad) break;
    v = b64map.indexOf(s.charAt(i));
    if (v < 0) continue;

    if (k == 0) {
      ret += int2char(v >> 2);
      slop = v & 3;
      k = 1;
    } else if (k == 1) {
      ret += int2char(slop << 2 | v >> 4);
      slop = v & 0xf;
      k = 2;
    } else if (k == 2) {
      ret += int2char(slop);
      ret += int2char(v >> 2);
      slop = v & 3;
      k = 3;
    } else {
      ret += int2char(slop << 2 | v >> 4);
      ret += int2char(v & 0xf);
      k = 0;
    }
  }

  if (k == 1) ret += int2char(slop << 2);
  return ret;
} // convert a base64 string to a byte/number array


function b64toBA(s) {
  //piggyback on b64tohex for now, optimize later
  var h = b64tohex(s);
  var i;
  var a = new Array();

  for (i = 0; 2 * i < h.length; ++i) {
    a[i] = parseInt(h.substring(2 * i, 2 * i + 2), 16);
  }

  return a;
}
/*
*
*
*
* SM
*
*
*
*
*
* */

/**
 SM2 TOOLS
 ct 20170215
 */


var SM = {
  convertInt: function convertInt(arr) {
    var out = new Array(parseInt(arr.length / 4));
    var tmp = new Array(4);

    for (var i = 0; i < arr.length; i += 4) {
      var tmp = arr.slice(i, i + 4);
      out[i / 4] = this.bigEndianByteToInt(tmp);
    }

    return out;
  },
  convertByte: function convertByte(arr) {
    var out = [];
    var tmp = [];

    for (var i = 0; i < arr.length; i++) {
      tmp = this.bigEndianIntToByte(arr[i]);

      for (var l = 0; l < tmp.length; l++) {
        out.push(tmp[l]);
      }
    }

    return out;
  },
  // 循环左移(int类型)  n:需要左移的数据; bitLen: 移动位数
  bitCycleLeft: function bitCycleLeft(n, bitLen) {
    bitLen %= 32;
    var tmp = this.bigEndianIntToByte(n);
    var byteLen = parseInt(bitLen / 8);
    var len = bitLen % 8;
    byteLen > 0 && (tmp = this.byteCycleLeft(tmp, byteLen));
    len > 0 && (tmp = this.bitSmall8CycleLeft(tmp, len));
    return this.bigEndianByteToInt(tmp);
  },
  // 循环左移 n:需要左移的数据; bitLen: 移动位数
  byteCycleLeft: function byteCycleLeft(n, byteLen) {
    var tmp = [];
    tmp = n.slice(byteLen, byteLen + n.length - byteLen);

    for (var i = 0; i < byteLen; i++) {
      tmp.push(n[i]);
    }

    return tmp;
  },
  // 高位int转化为byte数组
  bigEndianIntToByte: function bigEndianIntToByte(num) {
    return this.back(this.intToBytes(num));
  },
  // 组的位数值替换
  arraycopy: function arraycopy(a, aStart, b, bStart, len) {
    for (var i = 0; i < len; i++) {
      b[bStart + i] = a[aStart + i];
    }

    return b;
  },
  // 最低八位循环左移
  bitSmall8CycleLeft: function bitSmall8CycleLeft(n, len) {
    var tmp = new Array(n.length);
    var t1, t2, t3;

    for (var i = 0; i < tmp.length; i++) {
      t1 = (n[i] & 0x000000ff) << len;
      t2 = (n[(i + 1) % tmp.length] & 0x000000ff) >> 8 - len;
      t3 = t1 | t2;
      tmp[i] = t3;
    }

    return tmp;
  },
  bigEndianByteToInt: function bigEndianByteToInt(bytes) {
    return this.byteToInt(this.back(bytes));
  },
  back: function back(n) {
    var out = new Array(n.length);

    for (var i = 0; i < out.length; i++) {
      out[i] = n[out.length - i - 1];
    }

    return out;
  },
  longTobytes: function longTobytes(l) {
    var bytes = new Array(8);

    for (var i = 0; i < 8; i++) {
      bytes[i] = l >>> (7 - i) * 8;
      (7 - i) * 8 >= 32 && (bytes[i] = 0);
    }

    return bytes;
  },
  intToBytes: function intToBytes(num) {
    var bytes = new Array(4);
    bytes[0] = this.limitByte(0xff & num);
    bytes[1] = this.limitByte(0xff & num >> 8);
    bytes[2] = this.limitByte(0xff & num >> 16);
    bytes[3] = this.limitByte(0xff & num >> 24);
    return bytes;
  },
  byteToInt: function byteToInt(bytes) {
    var num = 0,
        temp;
    var limitBytes = this.limitByte(bytes);
    temp = 0x000000ff & limitBytes[0];
    num = num | temp;
    temp = (0x000000ff & limitBytes[1]) << 8;
    num = num | temp;
    temp = (0x000000ff & limitBytes[2]) << 16;
    num = num | temp;
    temp = (0x000000ff & limitBytes[3]) << 24;
    num = num | temp;
    return num;
  },
  byteConvert32Bytes: function byteConvert32Bytes(n) {
    var tmpd = [];
    if (n == null) return null;

    if (n.toByteArray().length == 33) {
      tmpd = n.toByteArray().slice(1, 33);
    } else if (n.toByteArray().length == 32) {
      tmpd = n.toByteArray();
    } else {
      tmpd = n.toByteArray();

      if (tmpd.length < 32) {
        for (var i = tmpd.length; i < 32; i++) {
          tmpd[i] = 0;
        }
      }
    }

    return tmpd;
  },
  intToByteArray: function intToByteArray(k) {
    return [this.limitByte(k >> 24 & 0xff), this.limitByte(k >> 16 & 0xff), this.limitByte(k >> 8 & 0xff), this.limitByte(k & 0xff)];
  },
  stringToBytes: function stringToBytes(str) {
    var utf8 = [];

    for (var i = 0; i < str.length; i++) {
      var charcode = str.charCodeAt(i);
      if (charcode < 0x80) utf8.push(charcode);else if (charcode < 0x800) {
        utf8.push(0xffffffc0 | charcode >> 6, 0xffffff80 | charcode & 0x3f);
      } else if (charcode < 0xd800 || charcode >= 0xe000) {
        utf8.push(0xffffffe0 | charcode >> 12, 0xffffff80 | charcode >> 6 & 0x3f, 0xffffff80 | charcode & 0x3f);
      } else {
        utf8.push(0xef, 0xbf, 0xbd);
      }
    }

    return utf8;
  },
  limitByte: function limitByte(obj) {
    if (typeof obj.length == 'undefined') {
      obj >= 128 && (obj -= 256);
    }

    for (var i = 0; i < obj.length; i++) {
      obj[i] >= 128 && (obj[i] -= 256);
    }

    return obj;
  },
  intToHex: function intToHex(obj) {
    var ind = 0,
        arr = [],
        res = [],
        out = '';
    var code = ['a', 'b', 'c', 'd', 'e', 'f'];

    for (var i = 0; ind < obj.length; ++ind) {
      arr[i++] = [(240 & obj[ind]) >>> 4];
      arr[i++] = [15 & obj[ind]];
    }

    for (var i = 0; i < arr.length; i++) {
      for (var k = 0; k < arr[i].length; k++) {
        res.push(arr[i][k]);
      }
    }

    for (var i = 0; i < res.length; i++) {
      var val = res[i];
      val >= 10 && (res[i] = code[val - 10]);
    }

    out = res.join('');
    return out;
  },
  hexToByte: function hexToByte(hex) {
    for (var bytes = [], c = 0; c < hex.length; c += 2) {
      bytes.push(parseInt(hex.substr(c, 2), 16));
    }

    return bytes;
  }
};
/*
*
*
* SM3
*
*
* */

/**
 SM2 v1.0
 ct 20170213
 */

var SM3 = {
  IV: function IV() {
    return SM.limitByte([0x73, 0x80, 0x16, 0x6f, 0x49, 0x14, 0xb2, 0xb9, 0x17, 0x24, 0x42, 0xd7, 0xda, 0x8a, 0x06, 0x00, 0xa9, 0x6f, 0x30, 0xbc, 0x16, 0x31, 0x38, 0xaa, 0xe3, 0x8d, 0xee, 0x4d, 0xb0, 0xfb, 0x0e, 0x4e]);
  },
  FirstPadding: function FirstPadding() {
    return SM.limitByte(0x80);
  },
  ZeroPadding: function ZeroPadding() {
    return SM.limitByte(0x00);
  },
  Tj: function Tj(j) {
    j < 16 ? j = 0x79cc4519 : j = 0x7a879d8a;
    return j;
  },
  FFj: function FFj(x, y, z, j) {
    if (j >= 0 && j <= 15) {
      return x ^ y ^ z;
    } else {
      return x & y | x & z | y & z;
    }
  },
  GGj: function GGj(x, y, z, j) {
    if (j >= 0 && j <= 15) {
      return x ^ y ^ z;
    } else {
      return x & y | ~x & z;
    }
  },
  P0: function P0(x) {
    var y = SM.bitCycleLeft(x, 9);
    var z = SM.bitCycleLeft(x, 17);
    return x ^ y ^ z;
  },
  P1: function P1(x) {
    return x ^ SM.bitCycleLeft(x, 15) ^ SM.bitCycleLeft(x, 23);
  },
  padding: function padding(source) {
    var out = [];
    var l = source.length * 8;
    var k = 448 - (l + 1) % 512;
    k < 0 && (k += 512);

    for (var i = 0; i < source.length; i++) {
      out.push(source[i]);
    }

    out.push(this.FirstPadding());
    var j = k - 7;

    while (j > 0) {
      out.push(this.ZeroPadding());
      j -= 8;
    }

    var sourceLongBytes = SM.longTobytes(l);

    for (var i = 0; i < sourceLongBytes.length; i++) {
      out.push(sourceLongBytes[i]);
    }

    return out;
  },
  expand: function expand(B) {
    var W = [];
    var W1 = [];
    W = B;

    for (var i = B.length; i < 68; i++) {
      W[i] = 0;
    }

    for (var i = 16; i < 68; i++) {
      W[i] = this.P1(W[i - 16] ^ W[i - 9] ^ SM.bitCycleLeft(W[i - 3], 15)) ^ SM.bitCycleLeft(W[i - 13], 7) ^ W[i - 6];
    }

    for (var i = 0; i < 64; i++) {
      W1[i] = W[i] ^ W[i + 4];
    }

    return [W, W1];
  },
  hash: function hash(source) {
    var obj = _typeof(source) == 'object' ? source : SM.stringToBytes(source);
    var padding = this.padding(obj);
    var n = parseInt(padding.length / (512 / 8));
    var b = [];
    var tempIv = this.IV();
    var result = [];

    for (var i = 0; i < n; i++) {
      var resPadding = padding.slice(i * 64, (i + 1) * 64);
      result = this.CFbyte(tempIv, resPadding);
      tempIv = result;
    }

    var resHex = SM.intToHex(result);
    return resHex;
  },
  CFbyte: function CFbyte(V, B) {
    var v, b;
    v = SM.convertInt(V);
    b = SM.convertInt(B);
    return SM.convertByte(this.CFint(v, b));
  },
  CFint: function CFint(V, B) {
    var a, b, c, d, e, f, g, h;
    var ss1, ss2, tt1, tt2;
    a = V[0];
    b = V[1];
    c = V[2];
    d = V[3];
    e = V[4];
    f = V[5];
    g = V[6];
    h = V[7];
    var arr = this.expand(B);
    var w = arr[0];
    var w1 = arr[1];

    for (var j = 0; j < 64; j++) {
      ss1 = SM.bitCycleLeft(a, 12) + e + SM.bitCycleLeft(this.Tj(j), j);
      ss1 = SM.bitCycleLeft(ss1, 7);
      ss2 = ss1 ^ SM.bitCycleLeft(a, 12);
      tt1 = this.FFj(a, b, c, j) + d + ss2 + w1[j];
      tt2 = this.GGj(e, f, g, j) + h + ss1 + w[j];
      d = c;
      c = SM.bitCycleLeft(b, 9);
      b = a;
      a = tt1;
      h = g;
      g = SM.bitCycleLeft(f, 19);
      f = e;
      e = this.P0(tt2);
    }

    var out = new Array(8);
    out[0] = a ^ V[0];
    out[1] = b ^ V[1];
    out[2] = c ^ V[2];
    out[3] = d ^ V[3];
    out[4] = e ^ V[4];
    out[5] = f ^ V[5];
    out[6] = g ^ V[6];
    out[7] = h ^ V[7];
    return out;
  }
};
/**
 阻止用户行为
 */
// document.oncontextmenu = function() {
//   return false;
// }
// document.onkeydown = function(e) {
//   var e = window.event || e;
//   var c = e.keyCode || e.which;
//   if (c == 123 || e.ctrlKey && c == 16 || e.ctrlKey && c == 83 || e.ctrlKey && c == 73 || e.ctrlKey && c == 75) return false;
// }

/**
 SM2 START
 */

window.SM2 = {
  ECC_ONLINE_PARAM: ["FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF", "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC", "28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93", "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123", "32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7", "BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0"],
  // 白皮书测试参数
  // ECC_ONLINE_PARAM: [
  //   "8542D69E4C044F18E8B92435BF6FF7DE457283915C45517D722EDB8B08F1DFC3",
  //   "787968B4FA32C3FD2417842E73BBFEFF2F3C848B6831D7E0EC65228B3937E498",
  //   "63E4C6D3B23B0C849CF84241484BFE48F61D59A5B16BA06E6E12D1DA27C5249A",
  //   "8542D69E4C044F18E8B92435BF6FF7DD297720630485628D5AE74EE7C32E79B7",
  //   "421DEBD61B62EAB6746434EBC3CC315E32220B3BADD50BDC4C4E6C147FEDD43D",
  //   "0680512BCBB42C07D47349D2153B70C4E5D7FDFCBFA36EA1A85841B9E46E09A2"
  // ],
  ecc: function ecc() {
    return {
      p: new BigInteger(this.ECC_ONLINE_PARAM[0]),
      a: new BigInteger(this.ECC_ONLINE_PARAM[1]),
      b: new BigInteger(this.ECC_ONLINE_PARAM[2]),
      n: new BigInteger(this.ECC_ONLINE_PARAM[3]),
      gx: new BigInteger(this.ECC_ONLINE_PARAM[4]),
      gy: new BigInteger(this.ECC_ONLINE_PARAM[5])
    };
  },
  encryptUseHex: function encryptUseHex(publicKey, plainText) {
    if (plainText == '' || typeof plainText == 'undefined') return {
      hex: '',
      b64: ''
    };
    var plainTextByte = _typeof(plainText) == 'object' ? plainText : SM.stringToBytes(plainText);
    var plaintTextCopy = [];

    for (var i = 0; i < plainTextByte.length; i++) {
      plaintTextCopy[i] = 0;
    }

    SM.arraycopy(plainTextByte, 0, plaintTextCopy, 0, plainTextByte.length);
    this.initialSM2Params();
    var c1 = this.getC1();
    var c2 = this.getC2(plainTextByte, publicKey); // 如果KDF全部为0，判断c2然后流程循环

    while (c2 == '') {
      this.initialSM2Params();
      c1 = this.getC1();
      c2 = this.getC2(plainTextByte, publicKey);
    }

    var c3 = this.getC3(plaintTextCopy);
    return {
      hex: (c1 + c2 + c3).toUpperCase(),
      b64: hex2b64(c1 + c2 + c3)
    };
  },
  encryptUseB64: function encryptUseB64(publicKey, plainText) {
    if (plainText == '' || typeof plainText == 'undefined') return {
      hex: '',
      b64: ''
    };
    var publicKeyHex = b64tohex(publicKey);
    return this.encryptUseHex(publicKeyHex, plainText);
  },
  initialSM2Params: function initialSM2Params() {
    this.eccCurve = new ECCurveFp(this.ecc().p, this.ecc().a, this.ecc().b);
    this.G = this.eccCurve.decodePointHex("04" + this.ECC_ONLINE_PARAM[4] + this.ECC_ONLINE_PARAM[5]);
    this.ec = new KJUR.crypto.ECDSA({
      'curve': 'sm2'
    });
    this.keypair = this.ec.generateKeyPairHex();
  },
  ecs: function ecs() {
    return this.ec;
  },
  keypairs: function keypairs() {
    return this.keypair;
  },
  k: function k() {
    return new BigInteger(this.keypairs().ecprvhex, 16);
  },
  getC1: function getC1() {
    return this.keypairs().ecpubhex;
  },
  getC2: function getC2(plainTextByte, publicKey) {
    var curveName = this.ecs().ecparams['curve'];
    var pubKeyPoint = ECPointFp.decodeFromHex(curveName, publicKey);
    this.p2 = pubKeyPoint.multiply(this.k());
    var x2 = this.p2.getX().toBigInteger();
    var y2 = this.p2.getY().toBigInteger();
    this.x2 = SM.byteConvert32Bytes(x2);
    this.y2 = SM.byteConvert32Bytes(y2);
    var temp = [];

    for (var i = 0; i < 64; i++) {
      temp[i] = 0;
    }

    SM.arraycopy(this.x2, 0, temp, 0, this.x2.length);
    SM.arraycopy(this.y2, 0, temp, this.x2.length, this.y2.length);
    this.t = this.KDF(temp, plainTextByte.length); // 判断如果KDF结果全为0，则返回空

    var count = 0;

    for (var i = 0; i < this.t.length; ++i) {
      this.t[i] == 0 && count++;
    }

    if (count == this.t.length) return '';
    var index = 0;

    for (var i = 0; i < plainTextByte.length; i++) {
      plainTextByte[i] ^= this.t[index++];
    }

    return SM.intToHex(plainTextByte);
  },
  getC3: function getC3(plainText) {
    var x2 = this.p2.getX().toBigInteger();
    var y2 = this.p2.getY().toBigInteger();
    this.x2 = SM.byteConvert32Bytes(x2);
    this.y2 = SM.byteConvert32Bytes(y2);
    var temp = [];
    var plainTextByte = typeof plainText == 'string' ? SM.stringToBytes(plainText) : plainText;

    for (var i = 0; i < 32 + 32 + plainTextByte.length; i++) {
      temp[i] = 0;
    }

    for (var i = 0; i < 32 + 32 + plainTextByte.length; i++) {
      temp[i] = 0;
    }

    SM.arraycopy(this.x2, 0, temp, 0, this.x2.length);
    SM.arraycopy(plainTextByte, 0, temp, this.x2.length, plainTextByte.length);
    SM.arraycopy(this.y2, 0, temp, this.x2.length + plainTextByte.length, this.y2.length);
    return SM3.hash(temp);
  },
  KDF: function KDF(Z, kLen) {
    var ct = 1;
    var ctByte = [],
        buffer = [],
        ctZ = [],
        digest = [];
    var digestLength = 32;
    var n = parseInt((kLen + 31) / 32);

    for (var l = 0; l < Z.length + 4; l++) {
      ctZ[l] = 0;
    }

    for (var l = 0; l < kLen; l++) {
      buffer[l] = 0;
    }

    for (var l = 0; l < Z.length; l++) {
      ctZ[l] = Z[l];
    }

    for (var i = 0; i < n; i++) {
      ctByte = SM.intToByteArray(ct);
      SM.arraycopy(ctByte, 0, ctZ, Z.length, ctByte.length);
      digest = SM.limitByte(SM.hexToByte(SM3.hash(ctZ)));

      if (i == n - 1) {
        if (kLen % 32 != 0) {
          digestLength = kLen % 32;
        }
      }

      SM.arraycopy(digest, 0, buffer, 32 * i, digestLength);
      ct++;
    }

    return buffer;
  }
};

//# sourceURL=webpack://idaasUtils/./src/plugins/SM2/sm2_all.js?