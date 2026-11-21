using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Version M1 of thmB_checks / thmB_vs_upper: the radius parameter m satisfies m*delta > 1 (article v5, Q64):
// delta = 1/k, m = k+1, h = ceil(log2 m)  (instead of m = 2k, h = ceil(log2 2k) of v1..v4).
// Part 1: exact check of  h*d <= M  at the formula M, worst case m = 2^h, delta = 1/k, k = 2..300 and k = 2^l (l = 1..60), forced exponents a_p(delta).
// Part 2: end-to-end pigeonhole on multiples of D (exact integers), exact strict test P_S(D t) < delta, small cases.
// Part 3: for k = 2..5000 and ten sets: exponent log2 D + M of Theorem 3.1 against L = ceil(a_S h^2 + a_S h) of Theorem 2.1 (both with the new h)
//         and against the old exponent (old h); decimal evaluation.
class P {
  static int Ceil2(BigInteger v) { int h = 0; while ((BigInteger.One << h) < v) h++; return h; }
  static int Forced(int p, int k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  static long CountN(int p, int a, BigInteger lim) { long n = a; while (BigInteger.Pow(p, (int)((n + 1) * (n + 1))) <= lim) n++; return n - a; }
  static long MOf(int[] ps, int[] a, int h, double A, out double Delta) {
    double al = a.Sum(); Delta = 0;
    for (int i = 0; i < ps.Length; i++) Delta += (double)a[i] * a[i] * Math.Log(ps[i], 2);
    double Q = (double)h * h * A * A - 4 * (h * al - Delta - h);
    double t = (h * A + Math.Sqrt(Math.Max(Q, 0))) / 2;
    return Math.Max(0, (long)Math.Ceiling(t * t - h - Delta));
  }
  static void Main() {
    Console.WriteLine("== Part 1: exact h*d <= M, m = k+1, h = ceil(log2(k+1)), forced exponents, worst case m = 2^h");
    var sets1 = new[]{ new[]{2}, new[]{3}, new[]{5}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{2,3,5,7}, new[]{101}, new[]{2,101}, new[]{2,3,5,7,11,13} };
    foreach (var S in sets1) {
      double A = S.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      var ks = Enumerable.Range(2, 299).Select(i => new BigInteger(i)).Concat(Enumerable.Range(1, 60).Select(l => BigInteger.One << l)).Distinct().ToList();
      int bad = 0, tested = 0; double maxRatio = 0;
      foreach (var kb in ks) {
        BigInteger m = kb + 1; int h = Ceil2(m);
        var a = S.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= kb) aa++; return aa; }).ToArray();
        double alpha = a.Sum(), Delta = S.Select((p, i) => (double)a[i] * a[i] * Math.Log(p, 2)).Sum();
        double disc = (double)h * h * A * A - 4 * (h * alpha - Delta - h);
        double ts = (h * A + Math.Sqrt(disc)) / 2;
        long M = Math.Max(0, (long)Math.Ceiling(ts * ts - h - Delta));
        BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= BigInteger.Pow(S[i], a[i] * a[i]);
        BigInteger lim = D * (BigInteger.One << (int)M) * (BigInteger.One << h);
        long d = 0; for (int i = 0; i < S.Length; i++) d += CountN(S[i], a[i], lim);
        tested++; if (h * d > M) bad++; if (M > 0) maxRatio = Math.Max(maxRatio, (double)h * d / M);
      }
      Console.WriteLine($"S={{{string.Join(",", S)}}} tested {tested} values of delta: violations {bad}, max h*d/M = {maxRatio:F4}");
    }
    Console.WriteLine("== Part 2: end-to-end pigeonhole on multiples of D, m = k+1 (exact), strict test P_S(Dt) < 1/k");
    foreach (var (ps, k) in new[]{ (new[]{2},3),(new[]{2},4),(new[]{2},5),(new[]{2},8),(new[]{3},3),(new[]{3},4),(new[]{5},6),(new[]{2,3},3),(new[]{2,3},4),(new[]{2,5},3),(new[]{2,5},4),(new[]{2,3},5) }) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      int m = k + 1; int h = Ceil2(m); var a = ps.Select(p => Forced(p, k)).ToArray();
      long M = MOf(ps, a, h, A, out double Dl);
      BigInteger D = 1; for (int i = 0; i < ps.Length; i++) D *= BigInteger.Pow(ps[i], a[i] * a[i]);
      if (M > 24) { Console.WriteLine($"skip S={{{string.Join(",", ps)}}} k={k} M={M}"); continue; }
      long N0 = 1L << (int)M; BigInteger K = D * N0;
      var coords = new List<BigInteger>();
      for (int i = 0; i < ps.Length; i++) for (int n = a[i] + 1; ; n++) { BigInteger q = BigInteger.Pow(ps[i], n * n); if (q > K * m) break; coords.Add(q); }
      int d = coords.Count; bool cond = BigInteger.Pow(m, d) <= N0;
      var seen = new Dictionary<string, long>(); long found = -1;
      for (long x = 0; x <= N0 && cond; x++) { BigInteger xx = D * x; var key = string.Join(",", coords.Select(q => (int)((m * (xx % q)) / q))); if (seen.TryGetValue(key, out long x0)) { found = x - x0; break; } seen[key] = x; }
      Func<BigInteger, bool> inBall = kv => { foreach (var p in ps) for (int n = 1; ; n++) { BigInteger q = BigInteger.Pow(p, n * n); if (q > kv * k) break; BigInteger r = kv % q; BigInteger dd = BigInteger.Min(r, q - r); if (dd * k >= q) return false; } return true; };
      bool ok = found > 0 && found <= N0 && inBall(D * found);
      Console.WriteLine($"S={{{string.Join(",", ps)}}} delta=1/{k} m={m} h={h} D={D} M={M} d={d} m^d<=2^M:{cond} t={found} t<=2^M and P_S(Dt)<delta:{ok}");
    }
    Console.WriteLine("== Part 3: delta=1/k, k=2..5000: exponents log2 D + M (Thm 3.1) and L (Thm 2.1); old h = ceil(log2 2k), new h = ceil(log2(k+1)); decimal");
    var sets = new List<int[]>{ new[]{2}, new[]{3}, new[]{5}, new[]{101}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{3,5,7}, new[]{2,3,5,7}, new[]{2,3,5,7,11,13} };
    foreach (var ps in sets) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double aS = Math.Max(1, A * A);
      int viol = 0; double maxRatio = 0, maxImp = 0, minImp = 1e9; int rows = 0;
      for (int k = 2; k <= 5000; k++) {
        var a = ps.Select(p => Forced(p, k)).ToArray();
        int hO = Ceil2(2L * k), hN = Ceil2(k + 1);
        long MO = MOf(ps, a, hO, A, out double Dl); double EO = Dl + MO;
        long MN = MOf(ps, a, hN, A, out double Dl2); double EN = Dl2 + MN;
        double LN = Math.Ceiling(aS * hN * hN + aS * hN);
        rows++; if (EN > LN + 1e-9) viol++; maxRatio = Math.Max(maxRatio, EN / LN);
        double imp = EN / EO; maxImp = Math.Max(maxImp, imp); minImp = Math.Min(minImp, imp);
      }
      Console.WriteLine($"S={{{string.Join(",", ps)}}} rows={rows} B_new>A_new violations={viol} max B_new/A_new={maxRatio:F3}  E_new/E_old: min={minImp:F3} max={maxImp:F3}");
    }
    foreach (var ps in new[]{ new[]{2,3}, new[]{2,3,5} }) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      foreach (int k in new[]{ 20, 80, 500, 5000 }) {
        var a = ps.Select(p => Forced(p, k)).ToArray(); int hO = Ceil2(2L * k), hN = Ceil2(k + 1);
        long MO = MOf(ps, a, hO, A, out double d1); long MN = MOf(ps, a, hN, A, out double d2);
        Console.WriteLine($"S={{{string.Join(",", ps)}}} k={k} hold={hO} Eold={d1 + MO:F2}  hnew={hN} Enew={d2 + MN:F2}");
      }
    }
  }
}
