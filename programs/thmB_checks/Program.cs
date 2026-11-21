using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Scope B: explicit bound on multiples of D_S(delta).
//  delta = 1/k (k>=2), m = ceil(2/delta) = 2k, h = ceil(log2 m), a_p = min{a : p^(2a+1) > k}, D = prod p^(a_p^2),
//  A = sum (log2 p)^(-1/2), alpha = sum a_p, Delta = log2 D = sum a_p^2 log2 p.
//  t* = (hA + sqrt(h^2 A^2 - 4(h alpha - Delta - h)))/2,  M = max(0, ceil(t*^2 - h - Delta)),  claim: exists t in [1, 2^M], k = D t, P_S(k) < delta.
//  Retained coordinates (p,n): n > a_p and p^(n^2) <= D 2^M m ; condition for pigeonhole: m^d <= 2^M, guaranteed by h*d <= M (m <= 2^h).
class P {
  static int Ceil2(BigInteger v) { int h = 0; while ((BigInteger.One << h) < v) h++; return h; }
  static int Apf(int p, int k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  // exact number of n > a with p^(n^2) <= lim
  static long CountN(int p, int a, BigInteger lim) {
    long n = a; while (BigInteger.Pow(p, (int)((n + 1) * (n + 1))) <= lim) n++; return n - a;
  }
  static void Main() {
    var sets = new int[][]{ new[]{2}, new[]{3}, new[]{5}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{2,3,5,7}, new[]{101}, new[]{2,101} };
    Console.WriteLine("== Part 1: exact check of  h*d_exact <= M  at the formula M (worst case m = 2^h), delta = 1/k for k = 2..300 and k = 2^l (l=1..60)");
    foreach (var S in sets) {
      double A = S.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      var ks = Enumerable.Range(2, 299).Select(i => new BigInteger(i)).Concat(Enumerable.Range(1, 60).Select(l => BigInteger.One << l)).Distinct().ToList();
      int bad = 0, tested = 0; double maxRatio = 0; int minSlack = int.MaxValue;
      foreach (var kk in ks) {
        int k = kk > 1000000000 ? 0 : (int)kk;
        BigInteger kb = kk;
        int h = Ceil2(2 * kb);
        var a = S.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= kb) aa++; return aa; }).ToArray();
        double alpha = a.Sum(), Delta = S.Select((p, i) => (double)a[i] * a[i] * Math.Log(p, 2)).Sum();
        double disc = (double)h * h * A * A - 4 * (h * alpha - Delta - h);
        double ts = (h * A + Math.Sqrt(disc)) / 2;
        long M = Math.Max(0, (long)Math.Ceiling(ts * ts - h - Delta));
        BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= BigInteger.Pow(S[i], a[i] * a[i]);
        BigInteger lim = D * (BigInteger.One << (int)M) * (BigInteger.One << h);
        long d = 0; for (int i = 0; i < S.Length; i++) d += CountN(S[i], a[i], lim);
        tested++;
        if (h * d > M) bad++;
        if (M > 0) maxRatio = Math.Max(maxRatio, (double)h * d / M);
      }
      Console.WriteLine($"S={{{string.Join(",", S)}}} tested {tested} values of delta: violations {bad}, max h*d/M = {maxRatio:F4}");
    }
    Console.WriteLine("== Part 2: end-to-end pigeonhole on multiples of D (exact), small cases");
    foreach (var (S, k) in new[]{ (new[]{2}, 4), (new[]{2}, 8), (new[]{2}, 16), (new[]{3}, 4), (new[]{2,3}, 4), (new[]{2,3}, 8), (new[]{5}, 6), (new[]{2,5}, 4) }) {
      double A = S.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      int m = 2 * k; int h = Ceil2(m);
      var a = S.Select(p => Apf(p, k)).ToArray();
      double alpha = a.Sum(), Delta = S.Select((p, i) => (double)a[i] * a[i] * Math.Log(p, 2)).Sum();
      double ts = (h * A + Math.Sqrt((double)h * h * A * A - 4 * (h * alpha - Delta - h))) / 2;
      int M = Math.Max(0, (int)Math.Ceiling(ts * ts - h - Delta));
      BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= BigInteger.Pow(S[i], a[i] * a[i]);
      if (M > 24) { Console.WriteLine($"skip S={{{string.Join(",", S)}}} k={k}: M={M}"); continue; }
      long N0 = 1L << M;
      BigInteger Kmax = D * N0;
      var coords = new List<(int p, BigInteger q)>();
      for (int i = 0; i < S.Length; i++) for (int n = a[i] + 1; ; n++) { BigInteger q = BigInteger.Pow(S[i], n * n); if (q > Kmax * m) break; coords.Add((S[i], q)); }
      int d = coords.Count; BigInteger boxes = BigInteger.Pow(m, d);
      bool cond = boxes <= N0;
      var seen = new Dictionary<string, long>(); long found = -1;
      for (long x = 0; x <= N0 && cond; x++) {
        BigInteger xx = D * x; var key = string.Join(",", coords.Select(c => (int)((m * (xx % c.q)) / c.q)));
        if (seen.TryGetValue(key, out long x0)) { found = x - x0; break; } seen[key] = x;
      }
      bool ok = false; long least = -1;
      Func<BigInteger, bool> inBall = kv => { foreach (var p in S) for (int n = 1; ; n++) { BigInteger q = BigInteger.Pow(p, n * n); if (q > kv * k) break; BigInteger r = kv % q; BigInteger dd = BigInteger.Min(r, q - r); if (dd * k >= q) return false; } return true; };
      // delta = 1/k, so ball: P < 1/k ; pigeonhole gives P < 1/m = 1/(2k) <= delta/2
      if (found > 0) ok = inBall(D * found);
      for (long t = 1; t <= 2000000 && least < 0; t++) if (inBall(D * t)) least = t;
      Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{k} m={m} h={h} D={D} M={M} N0=2^M d={d} m^d<=N0:{cond} pigeon t={found} P_S(D t)<delta:{ok} least t in ball={least}");
    }
    Console.WriteLine("== Part 3: exponents log2 u_S upper bounds, Scope B (2^(t*^2-h+1)) vs Thm upper' (L) vs old 4s^2h^2, delta = 2^-l");
    foreach (var S in new[]{ new[]{2}, new[]{2,3}, new[]{2,3,5} }) {
      double A = S.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double a2 = Math.Max(1, A * A); int s = S.Length;
      foreach (int l in new[]{ 4, 8, 16, 32, 64, 128 }) {
        BigInteger kb = BigInteger.One << l; int h = Ceil2(2 * kb);
        var a = S.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= kb) aa++; return aa; }).ToArray();
        double alpha = a.Sum(), Delta = S.Select((p, i) => (double)a[i] * a[i] * Math.Log(p, 2)).Sum();
        double ts = (h * A + Math.Sqrt((double)h * h * A * A - 4 * (h * alpha - Delta - h))) / 2;
        double B = Math.Max(Delta, ts * ts - h + 1), U = Math.Ceiling(a2 * h * h + a2 * h), O = 4.0 * s * s * h * h;
        Console.WriteLine($"S={{{string.Join(",", S)}}} l={l,3} h={h,3}  log2 D={Delta,9:F1}  ScopeB<= {B,9:F1}  Upper'<= {U,9:F0}  old<= {O,9:F0}   ratio B/Upper'={B / U:F3}  B/l^2={B / ((double)l * l):F3}");
      }
    }
  }
}
