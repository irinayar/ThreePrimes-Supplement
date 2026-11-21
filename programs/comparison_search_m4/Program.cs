using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Article v8 (Q67): sharp comparison D 2^M <= 2^L for a real eta (decimal, double precision).
// Notation: delta = 1/m, a_p = a_p(delta), Delta = sum a_p^2 log2 p, alpha = sum a_p, A = sum (log2 p)^(-1/2), a_S = max(1, A^2),
//           L = ceil(a_S eta^2 + a_S eta), Q = eta^2 A^2 - 4 (eta alpha - Delta - eta), t* = (eta A + sqrt Q)/2, M = max(0, ceil(t*^2 - eta - Delta)).
// Part 1: delta = 1/k, eta = log2 k, ten sets, k = 2..5000: rows with ceil(Delta) <= eta*alpha ("covered", Lean B_le_A_ceilM3: D 2^M <= 2^L), not covered, violations.
// Part 2: random real eta >= log2 m (3*10^6 cases, seed 99): covered / not covered / violations.
// Part 3: adversarial scans for Delta + M > L: (a) prime windows below m, m <= 4000, eta = log2 m + t; (b) all subsets of the 11 largest primes in windows (m(1-eps), m],
//         m <= 6*10^4; (c) exhaustive near m = 2^(n^2), n = 3..6, subsets of the 14 largest primes <= m, |m - 2^(n^2)| <= 500; (d) real-eta grid eta = log2 m + t, t in [0,1.5],
//         the c largest primes below m ~ 2^(n^2), n = 2..6. Reported: violations, max of Delta + M - L (all negative expected), smallest margins.
class P {
  static int Forced(int p, long k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  static bool IsPrimeSmall(int n) { if (n < 2) return false; for (int d = 2; (long)d * d <= n; d++) if (n % d == 0) return false; return true; }
  static ulong MulMod(ulong a, ulong b, ulong m) => (ulong)((UInt128)a * b % m);
  static ulong PowMod(ulong b, ulong e, ulong m) { ulong r = 1; b %= m; while (e > 0) { if ((e & 1) == 1) r = MulMod(r, b, m); b = MulMod(b, b, m); e >>= 1; } return r; }
  static bool IsPrime(ulong n) {
    if (n < 2) return false; foreach (ulong p in new ulong[]{ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 }) { if (n % p == 0) return n == p; }
    ulong d = n - 1; int s = 0; while ((d & 1) == 0) { d >>= 1; s++; }
    foreach (ulong a in new ulong[]{ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 }) {
      ulong x = PowMod(a, d, n); if (x == 1 || x == n - 1) continue; bool comp = true;
      for (int r = 1; r < s; r++) { x = MulMod(x, x, n); if (x == n - 1) { comp = false; break; } }
      if (comp) return false;
    }
    return true;
  }
  // returns excess Delta + M - L and the gap L + eta - 1 - t*^2
  static void Eval(double eta, double A, double Dl, double al, out double exc, out double gap, out double ceilD) {
    double aS = Math.Max(1, A * A);
    double Q = eta * eta * A * A - 4 * (eta * al - Dl - eta); double ts = (eta * A + Math.Sqrt(Math.Max(Q, 0))) / 2;
    double L = Math.Ceiling(aS * eta * eta + aS * eta); double M = Math.Max(0, Math.Ceiling(ts * ts - eta - Dl));
    exc = Dl + M - L; gap = (L + eta - 1) - ts * ts; ceilD = Math.Ceiling(Dl - 1e-12);
  }
  // (L + eta - c) - t*^2 with c = ceil(Delta) - Delta: the sharp bound is equivalent to this being >= 0
  static double GapC(double eta, double A, double Dl, double al, double ceilD) {
    double aS = Math.Max(1, A * A); double L = Math.Ceiling(aS * eta * eta + aS * eta);
    double Q = eta * eta * A * A - 4 * (eta * al - Dl - eta); double ts = (eta * A + Math.Sqrt(Math.Max(Q, 0))) / 2;
    return (L + eta - (ceilD - Dl)) - ts * ts;
  }
  static void Main() {
    Console.WriteLine("== Part 1: delta = 1/k, eta = log2 k, k = 2..5000; covered = (ceil(Delta) <= eta*alpha)");
    var sets = new List<int[]>{ new[]{2}, new[]{3}, new[]{5}, new[]{101}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{3,5,7}, new[]{2,3,5,7}, new[]{2,3,5,7,11,13} };
    foreach (var ps in sets) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); int notCov = 0, viol = 0, slackLt1 = 0, rows = 0, violAll = 0;
      for (int k = 2; k <= 5000; k++) {
        var a = ps.Select(p => Forced(p, k)).ToArray(); double eta = Math.Log(k, 2); double al = a.Sum(), Dl = 0; for (int i = 0; i < ps.Length; i++) Dl += (double)a[i] * a[i] * Math.Log(ps[i], 2);
        Eval(eta, A, Dl, al, out double exc, out double gap, out double cd); rows++;
        bool cov = eta * al >= cd - 1e-12; if (!cov) notCov++; if (eta * al - Dl < 1) slackLt1++;
        if (cov && (exc > 1e-9 || GapC(eta, A, Dl, al, cd) < -1e-9)) viol++; if (exc > 1e-9) violAll++;
      }
      Console.WriteLine($"S={{{string.Join(",", ps)}}} rows={rows} eta*alpha-Delta<1: {slackLt1}; not covered: {notCov}; violations of D2^M<=2^L among covered (and of t*^2<=L+eta-c): {viol}; violations of D2^M<=2^L overall: {violAll}");
    }
    Console.WriteLine("== Part 2: random real eta >= log2 m, random sets of 1-5 primes among 28 primes up to 1009, m in [2, 20000), 3000000 draws, seed 99");
    {
      var rnd = new Random(99); long tested = 0, cov = 0, bad = 0, notcov = 0, badAll = 0;
      var primes = new[]{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,211,1009};
      for (int it = 0; it < 3000000; it++) {
        int sz = rnd.Next(1, 6); var ps = primes.OrderBy(_ => rnd.Next()).Take(sz).OrderBy(x => x).ToArray();
        long m = rnd.Next(2, 20000); double eta = Math.Log(m, 2) + (rnd.Next(3) == 0 ? 0 : rnd.NextDouble() * 2);
        var a = ps.Select(p => Forced(p, m)).ToArray(); double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
        double al = a.Sum(), Dl = 0; for (int i = 0; i < ps.Length; i++) Dl += (double)a[i] * a[i] * Math.Log(ps[i], 2);
        Eval(eta, A, Dl, al, out double exc, out double gap, out double cd); tested++;
        if (exc > 1e-9) badAll++;
        if (eta * al >= cd - 1e-12) { cov++; if (exc > 1e-9) bad++; } else notcov++;
      }
      Console.WriteLine($"tested={tested} covered={cov} (violations {bad}) not covered={notcov}; violations of D2^M<=2^L overall={badAll}");
    }
    Console.WriteLine("== Part 3a: prime windows below m, m = 2..4000, eta = log2 m + t, t in {0, 0.1, 0.5, 0.9}");
    var allPrimes = Enumerable.Range(2, 70000).Where(IsPrimeSmall).ToArray();
    {
      var rnd = new Random(2026); long tested = 0, viol = 0; double maxEx = -1e9; string arg = "";
      for (int m = 2; m <= 4000; m++) {
        var below = allPrimes.Where(p => p <= m).ToArray(); var cands = new List<int[]>();
        foreach (double tau in new[]{ 1.0, 2.0, 4.0, 8.0, 16.0 }) { var s = below.Where(p => p > m / Math.Pow(2, 1.0 / tau)).ToArray(); if (s.Length > 0) cands.Add(s); }
        if (below.Length > 0) { cands.Add(below); cands.Add(below.Where(p => p > Math.Pow(m, 1.0 / 3)).ToArray()); }
        for (int r = 0; r < 12 && below.Length > 0; r++) { int sz = rnd.Next(1, Math.Min(10, below.Length) + 1); var pool = r % 2 == 0 ? below.Skip(Math.Max(0, below.Length - 40)).ToArray() : below; cands.Add(pool.OrderBy(_ => rnd.Next()).Take(Math.Min(sz, pool.Length)).OrderBy(x => x).ToArray()); }
        foreach (var ps in cands) {
          if (ps.Length == 0) continue; var a = ps.Select(p => Forced(p, m)).ToArray(); double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
          double al = a.Sum(), Dl = 0; for (int i = 0; i < ps.Length; i++) Dl += (double)a[i] * a[i] * Math.Log(ps[i], 2);
          foreach (double t in new[]{ 0.0, 0.1, 0.5, 0.9 }) { Eval(Math.Log(m, 2) + t, A, Dl, al, out double exc, out double gap, out double cd); tested++; if (exc > 1e-9) viol++; if (exc > maxEx && m >= 3) { maxEx = exc; arg = $"m={m} t={t} S={{{string.Join(",", ps.Take(8))}}}"; } }
        }
      }
      Console.WriteLine($"tested={tested} violations={viol}; max(Delta+M-L) over m>=3 = {maxEx:F4} at {arg} (m=2, S={{2}}: 0)");
    }
    Console.WriteLine("== Part 3b: all subsets of the 11 largest primes in (m(1-eps), m], eps in {0.01, 0.03, 0.08, 0.2}, m = 3..60000 (step 1 below 5000, then 7), eta = log2 m and log2 m + 0.3");
    {
      long tested = 0, viol = 0, gapNeg = 0; double maxEx = -1e9, minGap = 1e9; string argE = "", argG = "";
      for (int m = 3; m <= 60000; m += (m < 5000 ? 1 : 7)) {
        foreach (double eps in new[]{ 0.01, 0.03, 0.08, 0.2 }) {
          var win = allPrimes.Where(p => p <= m && p > m * (1 - eps)).ToArray(); if (win.Length == 0) continue; if (win.Length > 11) win = win.Skip(win.Length - 11).ToArray();
          int n = win.Length;
          for (int mask = 1; mask < (1 << n); mask++) {
            var ps = Enumerable.Range(0, n).Where(i => (mask >> i & 1) == 1).Select(i => win[i]).ToArray(); var a = ps.Select(p => Forced(p, m)).ToArray();
            double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double al = a.Sum(), Dl = 0; for (int i = 0; i < ps.Length; i++) Dl += (double)a[i] * a[i] * Math.Log(ps[i], 2);
            foreach (double t in new[]{ 0.0, 0.3 }) {
              Eval(Math.Log(m, 2) + t, A, Dl, al, out double exc, out double gap, out double cd); tested++; if (exc > 1e-9) viol++; if (gap < 0) gapNeg++;
              if (exc > maxEx) { maxEx = exc; argE = $"m={m} t={t} S={{{string.Join(",", ps.Take(8))}}}"; } if (gap < minGap) { minGap = gap; argG = $"m={m} t={t} n={ps.Length}"; }
            }
          }
        }
      }
      Console.WriteLine($"tested={tested} violations={viol}; max(Delta+M-L)={maxEx:F4} at {argE}; rows with L+eta-1-t*^2<0: {gapNeg}, min of it = {minGap:F4} at {argG}");
    }
    Console.WriteLine("== Part 3c: exhaustive near m = 2^(n^2): all subsets of the 14 largest primes <= m of sizes n-1..n+2, |m - 2^(n^2)| <= 500, eta = log2 m");
    foreach (int n0 in new[]{ 3, 4, 5, 6 }) {
      ulong center = 1UL << (n0 * n0); double maxExc = -1e9; string argE = ""; long tested = 0, viol = 0; var cache = new Dictionary<ulong, bool>();
      for (long off = -500; off <= 500; off++) {
        ulong m = (ulong)((long)center + off); var win = new List<ulong>();
        for (ulong q = m; win.Count < 14 && q > 2; q--) { if (!cache.TryGetValue(q, out bool pr)) { pr = IsPrime(q); cache[q] = pr; } if (pr) win.Add(q); }
        double eta = Math.Log2((double)m); int n = win.Count; var lam = win.Select(p => Math.Log2((double)p)).ToArray(); var inv = lam.Select(l => 1 / Math.Sqrt(l)).ToArray();
        for (int mask = 1; mask < (1 << n); mask++) {
          int c = 0; double A = 0, Dl = 0; for (int i = 0; i < n; i++) if ((mask >> i & 1) == 1) { c++; A += inv[i]; Dl += lam[i]; }
          if (c < n0 - 1 || c > n0 + 2) continue; Eval(eta, A, Dl, c, out double exc, out double gap, out double cd); tested++; if (exc > 1e-9) viol++;
          if (exc > maxExc) { maxExc = exc; argE = $"m=2^{n0 * n0}{off:+#;-#;+0} c={c}"; }
        }
      }
      Console.WriteLine($"n={n0} (eta~{n0 * n0}): tested={tested} violations={viol} max(Delta+M-L)={maxExc:E3} at {argE}");
    }
    Console.WriteLine("== Part 3d: real-eta grid: eta = log2 m + t, t in [0,1.5] (300000 points), the c largest primes below m, m = 2^(n^2) + off (off in -40,-32,..,40), c = n-1..n+1, n = 2..6");
    foreach (int n0 in new[]{ 2, 3, 4, 5, 6 }) {
      double bestExc = -1e9; string arg = ""; long viol = 0, tested = 0; ulong center = 1UL << (n0 * n0);
      for (int off = -40; off <= 40; off += 8) {
        ulong m = (ulong)((long)center + off); var win = new List<ulong>(); for (ulong q = m; win.Count < n0 + 2 && q > 2; q--) if (IsPrime(q)) win.Add(q);
        for (int c = Math.Max(1, n0 - 1); c <= n0 + 1 && c <= win.Count; c++) {
          var lam = win.Take(c).Select(p => Math.Log2((double)p)).ToArray(); double Dl = lam.Sum(); double A = lam.Sum(l => 1 / Math.Sqrt(l)); double eta0 = Math.Log2((double)m);
          for (long gi = 0; gi <= 300000; gi++) {
            double t = 1.5 * gi / 300000; Eval(eta0 + t, A, Dl, c, out double exc, out double gap, out double cd); tested++; if (exc > 1e-9) viol++;
            if (exc > bestExc) { bestExc = exc; arg = $"m=2^{n0 * n0}{off:+#;-#;+0} c={c} t={t:F5}"; }
          }
        }
      }
      Console.WriteLine($"n={n0}: tested={tested} violations={viol} max(Delta+M-L)={bestExc:F5} at {arg}");
    }
  }
}
