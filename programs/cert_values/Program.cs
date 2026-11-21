using System;
using System.Numerics;
// Exact check of D(k) = max{P_2(k-1), P_3(k), P_5(k)} at the two integers of TVGplusJoint_v19 Theorem (Cert).
class P {
  static (BigInteger, BigInteger) Pp(BigInteger k, int p) { k = BigInteger.Abs(k); BigInteger bn = 0, bd = 1; for (int n = 1; ; n++) { BigInteger q = BigInteger.Pow(p, n * n); BigInteger r = k % q; BigInteger d = BigInteger.Min(r, q - r); if (d * bd > bn * q) { bn = d; bd = q; } if (q > k * 1000) break; } return (bn, bd); }
  static void Main() {
    foreach (var (name, k) in new[] { ("k*", BigInteger.Parse("-14057403874393228150222683135")), ("h", BigInteger.Parse("3914458306129929505181663745")) }) {
      var a = Pp(k - 1, 2); var b = Pp(k, 3); var c = Pp(k, 5); var all = new[] { (a, 2), (b, 3), (c, 5) }; BigInteger bn = 0, bd = 1; int bp = 0;
      foreach (var ((n, d), p) in all) { Console.WriteLine($"  {name}: P_{p} term = {n}/{d} ({(double)(n * 1000000000000L / d) / 1e12:F12})"); if (n * bd > bn * d) { bn = n; bd = d; bp = p; } }
      BigInteger g = BigInteger.GreatestCommonDivisor(bn, bd);
      Console.WriteLine($"  {name}: D = {bn / g}/{bd / g} = {(double)(bn * 1000000000000L / bd) / 1e12:F12}, attained at prime {bp}; D < 1/57: {bn * 57 < bd}; D < 1/50: {bn * 50 < bd}");
    }
    Console.WriteLine($"claimed D(h) = 21611019521/1099511627776 = {21611019521.0 / 1099511627776.0:F12}");
  }
}
