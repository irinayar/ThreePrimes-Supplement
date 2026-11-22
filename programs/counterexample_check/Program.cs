using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
// Independent double-precision re-evaluation of the suspected counterexample: m = 65614, S = {largest prime <= m (a_p = 1)} + {three primes just above m (a_p = 0)}, delta = 1/m, real eta.
class P {
  static bool IsPrime(int n) { if (n < 2) return false; for (int d = 2; (long)d * d <= n; d++) if (n % d == 0) return false; return true; }
  static void Main() {
    int m = 65614; int pb = m; while (!IsPrime(pb)) pb--; var above = new List<int>(); for (int q = m + 1; above.Count < 3; q++) if (IsPrime(q)) above.Add(q);
    Console.WriteLine($"m={m}  prime below: {pb}  primes above: {string.Join(",", above)}");
    // forced exponents a_p(delta) with delta = 1/m: a = min{a : p^{-(2a+1)} < 1/m}
    var ps = new List<int>{ pb }; ps.AddRange(above);
    var a = ps.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= m) aa++; return aa; }).ToArray();
    Console.WriteLine("a_p = " + string.Join(",", a));
    double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double aS = Math.Max(1, A * A);
    double al = a.Sum(), Dl = 0; for (int i = 0; i < ps.Count; i++) Dl += (double)a[i] * a[i] * Math.Log(ps[i], 2);
    Console.WriteLine($"g={A:F12} g^2={A * A:F12} a_S={aS:F12} alpha={al} Delta={Dl:F12} log2 m={Math.Log(m, 2):F12}");
    double bestEx = -1e9; double bestEta = 0;
    foreach (double etaFix in new[]{ 16.0295, 16.0296, 16.03, 16.0302 }) { double eta = etaFix; double Q0 = eta * eta * A * A - 4 * (eta * al - Dl - eta); double ts0 = (eta * A + Math.Sqrt(Q0)) / 2; double y0 = ts0 * ts0 - eta - Dl; Console.WriteLine($"eta={eta} a_S(eta^2+eta)={aS * (eta * eta + eta):F6} L={Math.Ceiling(aS * (eta * eta + eta))} y={y0:F8} M={Math.Ceiling(y0)}  D*2^M/2^L = {Math.Pow(2, Dl + Math.Ceiling(y0) - Math.Ceiling(aS * (eta * eta + eta))):F6}"); }
    for (double t = 0; t <= 0.06; t += 0.00001) {
      double eta = Math.Log(m, 2) + t; double Q = eta * eta * A * A - 4 * (eta * al - Dl - eta); double ts = (eta * A + Math.Sqrt(Q)) / 2;
      double L = Math.Ceiling(aS * (eta * eta + eta)); double y = ts * ts - eta - Dl; double M = Math.Max(0, Math.Ceiling(y)); double ex = Dl + M - L;
      if (ex > bestEx) { bestEx = ex; bestEta = eta; }
      if (Math.Abs(t - 0) < 1e-12 || Math.Abs(t - 0.02) < 5e-6 || Math.Abs(t - 0.028) < 5e-6 || Math.Abs(t - 0.0286) < 5e-6 || Math.Abs(t - 0.03) < 5e-6) Console.WriteLine($"t={t:F5} eta={eta:F8} aS(eta^2+eta)={aS * (eta * eta + eta):F6} L={L} y={y:F6} M={M} Delta+M-L={ex:F6}");
    }
    Console.WriteLine($"max over the t grid: Delta+M-L = {bestEx:F6} at eta={bestEta:F8} (t={bestEta - Math.Log(m, 2):F6})");
    // the hypotheses: m*delta >= 1 with delta = 1/m; eta >= log2 m; eta >= 1; p^(2a_p-1) <= 1/delta for a_p >= 1
    Console.WriteLine($"check a_p lambda_p <= eta: {Math.Log(pb, 2):F6} <= {bestEta:F6}; eta*alpha={bestEta * al:F6} >= Delta={Dl:F6}; ceil(Delta)={Math.Ceiling(Dl)} > eta*alpha (open region)");
  }
}
