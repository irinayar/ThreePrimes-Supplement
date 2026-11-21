using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;

// Least positive k with P_S(k) < 1/R for S a set of primes, exactly: enumerate the ball of the sparsest prime up to X
// (depth-first lifting of admissible residues), test the other primes, double X until found.
class P {
  static int R; static Int128 X;
  class Pr { public int p; public Int128[] q; public int J; public Int128[] a; }
  static Pr Make(int p) {
    var qs = new List<Int128> { 1 };
    for (int j = 1; ; j++) { Int128 v = 1; for (int i = 0; i < j * j; i++) v *= p; if (v > (Int128)R * X) break; qs.Add(v); }
    var pr = new Pr { p = p, q = qs.ToArray() }; pr.J = pr.q.Length - 1; pr.a = new Int128[pr.J + 1];
    for (int j = 1; j <= pr.J; j++) pr.a[j] = (pr.q[j] + R - 1) / R - 1; return pr;
  }
  static Int128 CeilDiv(Int128 a, Int128 b) => (a + b - 1) / b;
  static bool Member(int p, Int128 x) {            // P_p(x) < 1/R for x >= 1 (levels with q <= R x suffice)
    Int128 q = 1; for (int j = 1; ; j++) { q = 1; for (int i = 0; i < j * j; i++) q *= p; if (q > (Int128)R * x) return true; Int128 r = x % q; Int128 d = r < q - r ? r : q - r; if (d * R >= q) return false; }
  }
  static long CountBall(Pr pr) { long c = 0; Dfs(pr, 1, 0, x => { c++; }); return c; }
  static void Dfs(Pr pr, int j, Int128 u, Action<Int128> f) {
    if (j > pr.J) { for (Int128 x = u; x <= X; x += pr.q[pr.J]) if (x >= 1) f(x); return; }
    Int128 qj = pr.q[j], qp = pr.q[j - 1], aj = pr.a[j];
    for (Int128 x = u; x <= aj && x < qj; x += qp) Dfs(pr, j + 1, x, f);
    Int128 lo = qj - aj; if (lo <= aj) lo = aj + 1;
    Int128 first = u + (lo - u > 0 ? CeilDiv(lo - u, qp) * qp : 0);
    for (Int128 x = first; x < qj; x += qp) Dfs(pr, j + 1, x, f);
  }
  static Int128 Least(int[] S, int k, double timeLimit, out Int128 Xused, out bool found) {
    R = k; var sw = Stopwatch.StartNew(); found = false; Xused = 0;
    for (X = 1000; X <= (Int128)1000000000000000000L * 1000; X *= 16) {
      Xused = X;
      var prs = S.Select(Make).ToArray();
      // choose sparsest: count with a cap by estimating via full count only for small X; use largest prime as heuristic then verify by count if cheap
      int best = 0; long bestCount = long.MaxValue;
      foreach (var i in Enumerable.Range(0, S.Length)) { long c = 0; try { c = CountBallCap(prs[i], 200000000); } catch { c = long.MaxValue; } if (c < bestCount) { bestCount = c; best = i; } }
      Int128 least = -1;
      var others = S.Where((p, i) => i != best).ToArray();
      Dfs(prs[best], 1, 0, x => { if (least >= 0 && x >= least) return; foreach (var p in others) if (!Member(p, x)) return; least = x; });
      if (least > 0) { found = true; return least; }
      if (sw.Elapsed.TotalSeconds > timeLimit) return -1;
    }
    return -1;
  }
  static long CountBallCap(Pr pr, long cap) { long c = 0; DfsCap(pr, 1, 0, ref c, cap); return c; }
  static void DfsCap(Pr pr, int j, Int128 u, ref long c, long cap) {
    if (c > cap) return;
    if (j > pr.J) { if (u >= 0) { Int128 n = u <= X ? (X - u) / pr.q[pr.J] + 1 : 0; c += (long)n; } return; }
    Int128 qj = pr.q[j], qp = pr.q[j - 1], aj = pr.a[j];
    for (Int128 x = u; x <= aj && x < qj; x += qp) DfsCap(pr, j + 1, x, ref c, cap);
    Int128 lo = qj - aj; if (lo <= aj) lo = aj + 1;
    Int128 first = u + (lo - u > 0 ? CeilDiv(lo - u, qp) * qp : 0);
    for (Int128 x = first; x < qj; x += qp) DfsCap(pr, j + 1, x, ref c, cap);
  }
  static int Apf(int p, int k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  static void Main(string[] args) {
    var S = args[0].Split(',').Select(int.Parse).ToArray(); int k0 = int.Parse(args[1]), k1 = int.Parse(args[2]); double tl = double.Parse(args[3]);
    // small sanity vs brute force
    {
      var S0 = new[] { 2, 3 };
      foreach (int k in new[] { 4, 8, 16 }) { var u = Least(S0, k, 60, out var xu, out var f); Console.WriteLine($"sanity S={{2,3}} k={k}: least={u} (expected 18, 480, 392688)"); }
    }
    foreach (int k in Enumerable.Range(k0, k1 - k0 + 1)) {
      var sw = Stopwatch.StartNew();
      var u = Least(S, k, tl, out var xu, out var found);
      BigInteger D = 1; foreach (var p in S) D *= BigInteger.Pow(p, Apf(p, k) * Apf(p, k));
      if (found) {
        double lg = BigInteger.Log((BigInteger)u); double L = Math.Log(k);
        int hh = 0; while ((BigInteger.One << hh) < 2 * k) hh++; double A = S.Sum(pp => 1 / Math.Sqrt(Math.Log(pp, 2))); var aa = S.Select(pp => Apf(pp, k)).ToArray(); double alpha = aa.Sum(), Delta = S.Select((pp, i) => (double)aa[i] * aa[i] * Math.Log(pp, 2)).Sum(); double Q = (double)hh * hh * A * A - 4 * (hh * alpha - Delta - hh); double ts = (hh * A + Math.Sqrt(Q)) / 2; double Bexp = Math.Max(Delta, ts * ts - hh + 1); double a2 = Math.Max(1, A * A); double Uexp = Math.Ceiling(a2 * hh * hh + a2 * hh); double l2u = lg / Math.Log(2); string chk = (l2u <= Bexp && l2u <= Uexp && u >= (Int128)(long)Math.Min((double)long.MaxValue, (double)D)) ? "bounds ok" : "BOUND VIOLATION"; Console.WriteLine($"   check: log2 u={l2u:F1} <= ThmB {Bexp:F1}, <= Upper {Uexp:F0}: {chk}");
        Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{k}: u={u}  D_S={D}  u/D={(double)(BigInteger)u / (double)D:G6}  ln u={lg:F2}  ln u/L^2={lg / (L * L):F3}  [{sw.Elapsed.TotalSeconds:F1}s, X<={xu}]");
      } else Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{k}: not found within time limit (searched X up to {xu}) [{sw.Elapsed.TotalSeconds:F1}s]");
    }
  }
}
