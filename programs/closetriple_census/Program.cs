using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;

class P {
  const int PREC = 160;                       // fixed-point fractional bits
  static BigInteger ONE = BigInteger.One << PREC;
  // atanh(1/k) * 2 in fixed point (series), exact enough: error < 2^-150
  static BigInteger TwoAtanh(int k) {
    BigInteger term = ONE / k, sum = BigInteger.Zero; BigInteger k2 = (BigInteger)k * k;
    for (int i = 1; term > 0; i += 2) { sum += term / i; term /= k2; }
    return 2 * sum;
  }
  static BigInteger ln2, ln3, ln5;
  static BigInteger Sq(long n) => (BigInteger)n * n;
  static BigInteger LogP(int p, long n) => Sq(n) * (p == 2 ? ln2 : p == 3 ? ln3 : ln5);
  static void Main(string[] args) {
    long NMAX = long.Parse(args[0]);
    ln2 = 2 * TwoAtanh(3) / 2 * 1;              // ln2 = 2 atanh(1/3)
    ln2 = TwoAtanh(3);
    ln3 = ln2 + TwoAtanh(5);                    // ln3 = ln2 + ln(3/2) = ln2 + 2 atanh(1/5)
    ln5 = 2 * ln2 + TwoAtanh(9);                // ln5 = ln4 + ln(5/4) = 2 ln2 + 2 atanh(1/9)
    double d2 = Math.Log(2), d3 = Math.Log(3), d5 = Math.Log(5);
    Console.WriteLine($"ln2 check {(double)(ln2 >> 100) / Math.Pow(2, 60):F15} vs {d2:F15}; ln3 {(double)(ln3 >> 100) / Math.Pow(2, 60):F15} vs {d3:F15}; ln5 {(double)(ln5 >> 100) / Math.Pow(2, 60):F15} vs {d5:F15}");
    int[] As = { 1, 2, 5, 10 };
    var found = new Dictionary<int, List<(long n, long m, long l)>>();
    foreach (var A in As) found[A] = new List<(long, long, long)>();
    int Amax = As.Max();
    for (long n = 32; n <= NMAX; n++) {
      int fl = 63 - BitOperations.LeadingZeroCount((ulong)n);          // floor(log2 n)
      double W = (1.0 + fl) * (1.0 + fl) * d2;
      double x = (double)n * n * d2, slack = Amax * W + 2.0;
      // candidates m with |m^2 ln3 - x| <= slack
      long m0 = (long)Math.Ceiling(Math.Sqrt(Math.Max(0, x - slack) / d3)), m1 = (long)Math.Floor(Math.Sqrt((x + slack) / d3));
      if (m1 < m0) continue;
      long l0 = (long)Math.Ceiling(Math.Sqrt(Math.Max(0, x - slack) / d5)), l1 = (long)Math.Floor(Math.Sqrt((x + slack) / d5));
      if (l1 < l0) continue;
      for (long m = m0 - 1; m <= m1 + 1; m++) for (long l = l0 - 1; l <= l1 + 1; l++) {
        BigInteger a = LogP(2, n), b = LogP(3, m), c = LogP(5, l);
        BigInteger mn = BigInteger.Min(a, BigInteger.Min(b, c)), mx = BigInteger.Max(a, BigInteger.Max(b, c));
        BigInteger Wfix = (BigInteger)((1 + fl) * (1 + fl)) * ln2;
        // other periods strictly inside [mn,mx] besides the members
        bool ok = true;
        int[] ps = { 2, 3, 5 }; long[] idx = { n, m, l };
        for (int t = 0; t < 3 && ok; t++) {
          BigInteger lp = t == 0 ? ln2 : t == 1 ? ln3 : ln5;
          long lo = (long)Math.Ceiling(Math.Sqrt((double)((mn >> 100)) / Math.Pow(2, 60) / (t == 0 ? d2 : t == 1 ? d3 : d5))) - 2;
          long hi = (long)Math.Floor(Math.Sqrt((double)((mx >> 100)) / Math.Pow(2, 60) / (t == 0 ? d2 : t == 1 ? d3 : d5))) + 2;
          for (long q = Math.Max(1, lo); q <= hi; q++) {
            if (q == idx[t]) continue;
            BigInteger v = Sq(q) * lp;
            if (v >= mn && v <= mx) { ok = false; break; }
          }
        }
        if (!ok) continue;
        BigInteger diam = mx - mn;
        foreach (var A in As) if (diam <= A * Wfix) found[A].Add((n, m, l));
      }
    }
    foreach (var A in As) {
      var L = found[A].OrderBy(t => t.n).ToList();
      Console.WriteLine($"A={A}: count={L.Count} largest n={(L.Count > 0 ? L.Last().n : 0)}  (n in [32,{NMAX}])");
    }
    Console.WriteLine("A=1 list (n,m,l): " + string.Join(" ", found[1].OrderBy(t => t.n).Select(t => $"({t.n},{t.m},{t.l})")));
  }
}
