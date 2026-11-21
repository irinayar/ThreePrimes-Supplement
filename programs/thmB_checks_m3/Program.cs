using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Version M3 (article v7, Q66): the real eta = log2 m replaces h = ceil(log2 m); delta = 1/k, m = k (m*delta >= 1).
// Part 1: exact BigInteger check of the counting conditions with the EXACT m:
//         Thm 3.1: m^d <= 2^M, d = sum_p #{n > a_p : p^(n^2) <= D 2^M m};  Thm 2.1: m^d <= 2^L, d = sum_p #{n >= 1 : p^(n^2) <= 2^L m}.
//         k = 2..5000 and five larger k, ten sets; M, L formed in double precision; also the slack eta*alpha - Delta and the decimal comparison Delta+M <= L.
// Part 2: end-to-end pigeonhole on multiples of D (exact integers, exact strict test P_S(Dt) < 1/k) with m = k not a power of 2.
// Part 3: old (h = ceil(log2 k), v6) against new (eta = log2 k) exponents log2 D + M.
// Part 4: random test (random prime sets, random real delta): comparison Delta+M <= L and exact counting.
// Part 5: dense decimal test of Delta+M <= L for 26 single primes and 7 small sets, m = 2..2*10^6.
class P {
  static int Forced(int p, BigInteger k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  static int Ceil2(int v) { int h = 0; while ((1L << h) < v) h++; return h; }
  static long CountN(int p, int a, BigInteger lim) { long n = a; while (BigInteger.Pow(p, (int)((n + 1) * (n + 1))) <= lim) n++; return n - a; }
  static long MOf(int[] ps, int[] a, double h, double A, out double Delta, out double Alpha) {
    Alpha = a.Sum(); Delta = 0;
    for (int i = 0; i < ps.Length; i++) Delta += (double)a[i] * a[i] * Math.Log(ps[i], 2);
    double Q = h * h * A * A - 4 * (h * Alpha - Delta - h);
    double t = (h * A + Math.Sqrt(Math.Max(Q, 0))) / 2;
    return Math.Max(0, (long)Math.Ceiling(t * t - h - Delta));
  }
  static void Main() {
    var sets = new List<int[]>{ new[]{2}, new[]{3}, new[]{5}, new[]{101}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{3,5,7}, new[]{2,3,5,7}, new[]{2,3,5,7,11,13} };
    var ks = Enumerable.Range(2, 4999).ToList(); ks.AddRange(new[]{ 10000, 100000, 1000000, 1048577, 1073741825 });
    Console.WriteLine("== Part 1: exact counting with the exact m = k, real eta = log2 k, forced exponents; slack = eta*alpha - Delta");
    foreach (var ps in sets) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double aS = Math.Max(1, A * A);
      int bad31 = 0, bad21 = 0, viol = 0, rows = 0, slackLt1 = 0, slackNeg = 0; double maxRatio = 0, minRel = 1, maxRel = 0, maxExcessLt1 = -1e9, maxExcessAll = -1e9;
      foreach (int k in ks) {
        double eta = Math.Log(k, 2); int h = Ceil2(k);
        var a = ps.Select(p => Forced(p, k)).ToArray();
        long Mh = MOf(ps, a, h, A, out double Dl, out double al); double Eh = Dl + Mh;
        long Me = MOf(ps, a, eta, A, out double Dl2, out double al2); double Ee = Dl2 + Me;
        BigInteger D = 1; for (int i = 0; i < ps.Length; i++) D *= BigInteger.Pow(ps[i], a[i] * a[i]);
        BigInteger lim = D * (BigInteger.One << (int)Me) * k; long d = 0; for (int i = 0; i < ps.Length; i++) d += CountN(ps[i], a[i], lim);
        if (BigInteger.Pow(k, (int)d) > (BigInteger.One << (int)Me)) bad31++;
        long L = (long)Math.Ceiling(aS * eta * eta + aS * eta);
        BigInteger lim2 = (BigInteger.One << (int)L) * k; long d2 = 0; for (int i = 0; i < ps.Length; i++) d2 += CountN(ps[i], 0, lim2);
        if (BigInteger.Pow(k, (int)d2) > (BigInteger.One << (int)L)) bad21++;
        double ex = Ee - L; maxExcessAll = Math.Max(maxExcessAll, ex); if (ex > 1e-9) viol++; maxRatio = Math.Max(maxRatio, Ee / L);
        double slack = eta * al2 - Dl2; if (slack < 0) slackNeg++; if (slack < 1) { slackLt1++; maxExcessLt1 = Math.Max(maxExcessLt1, ex); }
        double rel = Ee / Eh; minRel = Math.Min(minRel, rel); maxRel = Math.Max(maxRel, rel); rows++;
      }
      Console.WriteLine($"S={{{string.Join(",", ps)}}} rows={rows} exact fails Thm3.1={bad31} Thm2.1={bad21} | Delta+M>L violations={viol} max(Delta+M-L)={maxExcessAll:F4} max ratio={maxRatio:F3} | rows with slack<1: {slackLt1} (slack<0: {slackNeg}), max(Delta+M-L) there={(slackLt1 > 0 ? maxExcessLt1.ToString("F4") : "-")} | E_eta/E_h: min={minRel:F3} max={maxRel:F3}");
    }
    Console.WriteLine("== Part 2: end-to-end pigeonhole on multiples of D, m = k (exact), real eta = log2 k, strict test P_S(Dt) < 1/k");
    foreach (var (ps, k) in new[]{ (new[]{2},3),(new[]{2},5),(new[]{2},6),(new[]{2},7),(new[]{3},3),(new[]{3},5),(new[]{5},6),(new[]{5},7),(new[]{2,3},3),(new[]{2,3},5),(new[]{2,3},6),(new[]{2,5},3),(new[]{2,5},5),(new[]{3,5},3) }) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      int m = k; double eta = Math.Log(m, 2); var a = ps.Select(p => Forced(p, k)).ToArray();
      long M = MOf(ps, a, eta, A, out double Dl, out double al);
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
      Console.WriteLine($"S={{{string.Join(",", ps)}}} delta=1/{k} m={m} eta={eta:F3} (h={Ceil2(k)}) D={D} M={M} d={d} m^d<=2^M:{cond} t={found} t<=2^M and P_S(Dt)<delta:{ok}");
    }
    Console.WriteLine("== Part 3: exponent log2 D + M, old h = ceil(log2 k) (version 6) against new real eta = log2 k (version 7), forced exponents, decimal");
    foreach (var ps in new[]{ new[]{2,3}, new[]{2,3,5} }) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      foreach (int k in new[]{ 17, 20, 33, 65, 80, 129, 500, 513, 5000 }) {
        var a = ps.Select(p => Forced(p, k)).ToArray(); int h = Ceil2(k); double eta = Math.Log(k, 2);
        long Mh = MOf(ps, a, h, A, out double d1, out double a1); long Me = MOf(ps, a, eta, A, out double d2, out double a2);
        Console.WriteLine($"S={{{string.Join(",", ps)}}} k={k} h={h} E_h={d1 + Mh:F2}  eta={eta:F3} E_eta={d2 + Me:F2}  ratio={(d2 + Me) / (d1 + Mh):F3}");
      }
    }
    Console.WriteLine("== Part 4: random test: random sets of 1-5 primes among 28 primes (up to 1009), delta random real in 2^-1..2^-13 (every 4th: 1/k, k<20000), m = ceil(1/delta), eta = log2 m, seed 12345, 200000 draws");
    {
      var primes = new[]{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,211,1009};
      var rnd = new Random(12345); int N = 200000; int viol = 0, exactFail = 0, tested = 0; double maxExcess = -1e9;
      for (int it = 0; it < N; it++) {
        int sz = rnd.Next(1, 6); var ps = primes.OrderBy(_ => rnd.Next()).Take(sz).OrderBy(x => x).ToArray();
        double delta = Math.Pow(2, -(1 + rnd.NextDouble() * 12)); if (it % 4 == 0) delta = 1.0 / rnd.Next(2, 20000);
        BigInteger m = (BigInteger)Math.Ceiling(1 / delta); if (m < 2) continue; tested++;
        double eta = BigInteger.Log(m, 2);
        var a = ps.Select(p => { int aa = 0; while (Math.Pow(p, -(2.0 * aa + 1)) >= delta) aa++; return aa; }).ToArray();
        double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double aS = Math.Max(1, A * A);
        long M = MOf(ps, a, eta, A, out double Dl, out double al); long L = (long)Math.Ceiling(aS * eta * eta + aS * eta);
        double ex = Dl + M - L; maxExcess = Math.Max(maxExcess, ex); if (ex > 1e-9) viol++;
        BigInteger D = 1; for (int i = 0; i < ps.Length; i++) D *= BigInteger.Pow(ps[i], a[i] * a[i]);
        BigInteger lim = D * (BigInteger.One << (int)M) * m; long d = 0; for (int i = 0; i < ps.Length; i++) d += CountN(ps[i], a[i], lim);
        if (BigInteger.Pow(m, (int)d) > (BigInteger.One << (int)M)) exactFail++;
      }
      Console.WriteLine($"tests={tested} Delta+M<=L violations={viol} max(Delta+M-L)={maxExcess:F4} exact counting failures={exactFail}");
    }
    Console.WriteLine("== Part 5: dense decimal test of Delta+M <= L, m = 2..2*10^6 (step 1 up to 2*10^5, then 97), a_p = a_p(1/m)");
    {
      var primes = new[]{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101};
      var sets5 = primes.Select(p => new[]{p}).Concat(new[]{ new[]{2,3}, new[]{3,5}, new[]{3,7}, new[]{5,7}, new[]{2,3,5}, new[]{3,5,7}, new[]{3,5,7,11} }).ToList();
      int totalViol = 0; long tested = 0; double maxEx = -1e9;
      foreach (var ps in sets5) {
        double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double aS = Math.Max(1, A * A);
        for (long m = 2; m <= 2000000; m += (m < 200000 ? 1 : 97)) {
          double eta = Math.Log(m, 2); var a = ps.Select(p => Forced(p, m)).ToArray();
          long M = MOf(ps, a, eta, A, out double Dl, out double al); long L = (long)Math.Ceiling(aS * eta * eta + aS * eta);
          double ex = Dl + M - L; tested++; maxEx = Math.Max(maxEx, ex); if (ex > 1e-9) totalViol++;
        }
      }
      Console.WriteLine($"sets={sets5.Count} tested={tested} violations={totalViol} max(Delta+M-L)={maxEx:F4}");
    }
  }
}
