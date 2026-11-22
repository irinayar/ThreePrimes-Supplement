using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Threading.Tasks;

// Exact scan over ALL real eta >= log2 m (256-bit fixed point). For fixed m and a set S (a_p = a_p(1/m)), a_S = max(1,A^2) is constant, so
// L(eta) = ceil(a_S (eta^2 + eta)) is constant on the intervals (eta_{K-1}, eta_K] where a_S(eta_K^2 + eta_K) = K, while M(eta) = ceil(t*^2 - eta - Delta)_+ is nondecreasing in eta
// on those intervals (checked numerically below through the value at the right end only: the maximum of Delta + M - L on the interval is at the right end).
// So the maximum of the excess Delta + M - L over eta in [log2 m, log2 m + Tspan] is the maximum over the breakpoints K of  Delta + ceil(y(eta_K))_+ - K.
class P {
  const int PREC = 256;
  static readonly BigInteger F = BigInteger.One << PREC;
  static BigInteger ISqrt(BigInteger n) { if (n.IsZero) return 0; int bl = (int)n.GetBitLength(); BigInteger x = BigInteger.One << ((bl + 1) / 2); while (true) { BigInteger y = (x + n / x) >> 1; if (y >= x) return x; x = y; } }
  static BigInteger SqrtFP(BigInteger x) => ISqrt(x * F);
  static BigInteger Log2FP(BigInteger x) {
    int k = (int)x.GetBitLength() - 1; BigInteger r = (x << PREC) >> k; BigInteger res = (BigInteger)k << PREC;
    for (int i = 1; i <= PREC; i++) { r = (r * r) >> PREC; if (r >= (F << 1)) { r >>= 1; res |= BigInteger.One << (PREC - i); } }
    return res;
  }
  static bool IsPrime(BigInteger n) {
    if (n < 2) return false;
    foreach (int p in new[]{ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53 }) { if (n % p == 0) return n == p; }
    BigInteger d = n - 1; int s = 0; while (d.IsEven) { d >>= 1; s++; }
    foreach (int a in new[]{ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53 }) {
      BigInteger x = BigInteger.ModPow(a, d, n); if (x == 1 || x == n - 1) continue; bool comp = true;
      for (int r = 1; r < s; r++) { x = BigInteger.ModPow(x, 2, n); if (x == n - 1) { comp = false; break; } }
      if (comp) return false;
    }
    return true;
  }
  static double ToDouble(BigInteger fp) => (double)fp / (double)F;
  static BigInteger CeilFP(BigInteger y) { if (y <= 0) return 0; return (y + F - 1) / F; }
  // Scan: Delta, alpha (integer), A (all FP), eta0 = log2 m; returns max over breakpoints K of (Delta + M - K) as FP, and the arg (K, t)
  static BigInteger ScanBreakpoints(BigInteger Dl, int al, BigInteger A, BigInteger eta0, double Tspan, out string arg, out long nBreak) {
    BigInteger A2 = (A * A) >> PREC; BigInteger aS = BigInteger.Max(F, A2);
    // L0(eta) = aS (eta^2 + eta); at eta0:
    BigInteger e0sq = (eta0 * eta0) >> PREC; BigInteger L0 = ((aS * e0sq) >> PREC) + ((aS * eta0) >> PREC);
    BigInteger Klo = (L0 + F - 1) / F; BigInteger best = BigInteger.MinusOne << (PREC + 12); arg = ""; nBreak = 0;
    BigInteger etaMax = eta0 + ((BigInteger)(long)(Tspan * 1000000) << PREC) / 1000000; BigInteger Kmax = ((aS * ((etaMax * etaMax) >> PREC) >> PREC) + (aS * etaMax >> PREC)) / F + 1;
    for (BigInteger K = Klo; K <= Kmax; K++) {
      BigInteger ratio = ((K << (2 * PREC)) / aS); // K / aS in FP
      BigInteger eta = (SqrtFP(F + 4 * ratio) - F) / 2; // solves eta^2 + eta = K/aS
      if (eta < eta0) eta = eta0; // interval K starts below eta0: its right end is >= eta0 (K >= ceil(L0(eta0)))
      BigInteger e2 = (eta * eta) >> PREC;
      BigInteger Qt = ((e2 * A2) >> PREC) - 4 * (eta * al - Dl - eta); if (Qt < 0) Qt = 0;
      BigInteger ts = (((eta * A) >> PREC) + SqrtFP(Qt)) / 2; BigInteger t2 = (ts * ts) >> PREC;
      BigInteger y = t2 - eta - Dl; BigInteger M = CeilFP(y);
      BigInteger exc = Dl + (M << PREC) - (K << PREC); nBreak++;
      if (exc > best) { best = exc; arg = $"K={K} t={ToDouble(eta - eta0):F6} M={M}"; }
    }
    return best;
  }
  static void Main(string[] args) {
    string mode = args.Length > 0 ? args[0] : "family";
    if (mode == "family") {
      int[] ns = args.Length > 1 ? args.Skip(1).Select(int.Parse).ToArray() : new[]{ 3, 4, 5, 6, 7, 8, 9, 10 };
      foreach (int n0 in ns) {
        BigInteger center = BigInteger.One << (n0 * n0); var cache = new System.Collections.Concurrent.ConcurrentDictionary<BigInteger, bool>();
        int[] offs = new[]{ -900, -600, -400, -300, -200, -150, -100, -60, -30, -10, 0, 10, 30, 60, 100, 200, 400 };
        double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0, breaks = 0; object lk = new object();
        Parallel.ForEach(offs, off => {
          BigInteger m = center + off; var win = new List<BigInteger>(); for (BigInteger q = m; win.Count < 14 && q > 2; q--) { if (cache.GetOrAdd(q, IsPrime)) win.Add(q); }
          BigInteger eta0 = Log2FP(m); int n = win.Count; var lam = win.Select(Log2FP).ToArray(); var inv = lam.Select(l => (F * F) / SqrtFP(l)).ToArray();
          double lb = -1e9; string la = ""; long lc = 0, lv = 0, lbk = 0;
          for (int mask = 1; mask < (1 << n); mask++) {
            int c = 0; BigInteger A = 0, Dl = 0; for (int i = 0; i < n; i++) if ((mask >> i & 1) == 1) { c++; A += inv[i]; Dl += lam[i]; }
            if (c < n0 - 1 || c > n0 + 1) continue;
            BigInteger e = ScanBreakpoints(Dl, c, A, eta0, 2.0, out string arg, out long nb); double ed = ToDouble(e); lc++; lbk += nb; if (e > 0) lv++;
            if (ed > lb) { lb = ed; la = $"off={off} c={c} mask={mask} {arg}"; }
          }
          lock (lk) { cases += lc; viol += lv; breaks += lbk; if (lb > bestExc) { bestExc = lb; bestArg = la; } }
        });
        Console.WriteLine($"n={n0}: (m,S) cases={cases}, breakpoints scanned={breaks}, violations={viol}; max over all real eta in [log2 m, log2 m + 2] of Delta+M-L = {bestExc:E6} at {bestArg}");
      }
    } else if (mode == "nearn") {
      // m uniformly in [2^(n^2) (1 - w/n^2), 2^(n^2) (1 + w/n^2)] (w = 3): eta = log2 m ~ n^2 + tau with |tau| <~ 2/n^2; primes just below m; sizes n-1..n+1; breakpoints for eta in [log2 m, log2 m + 0.3]
      int n0 = int.Parse(args[1]); int N = int.Parse(args[2]); var rnd = new Random(4000 + n0); var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray();
      BigInteger center = BigInteger.One << (n0 * n0); double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0; object lk = new object();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); long u = r.Next(-(1 << 20), 1 << 20); BigInteger m = center + (center * 3 * u) / ((BigInteger)(n0 * n0) << 20);
        var win = new List<BigInteger>(); for (BigInteger q = m; win.Count < 12 && q > 2; q--) if (IsPrime(q)) win.Add(q);
        BigInteger eta0 = Log2FP(m); int n = win.Count; var lam = win.Select(Log2FP).ToArray(); var inv = lam.Select(l => (F * F) / SqrtFP(l)).ToArray();
        for (int mask = 1; mask < (1 << n); mask++) {
          int c = 0; BigInteger A = 0, Dl = 0; for (int i = 0; i < n; i++) if ((mask >> i & 1) == 1) { c++; A += inv[i]; Dl += lam[i]; }
          if (c < n0 - 1 || c > n0 + 1) continue;
          BigInteger e = ScanBreakpoints(Dl, c, A, eta0, 0.3, out string arg, out long nb); double ed = ToDouble(e);
          lock (lk) { cases++; if (e > 0) { viol++; if (viol <= 10) Console.WriteLine($"VIOLATION n={n0} m={m} c={c} mask={mask} {arg} excess={ed:E4}"); } if (ed > bestExc) { bestExc = ed; bestArg = $"tau={ToDouble(eta0) - n0 * n0:E3} c={c} mask={mask} {arg}"; } }
        }
      });
      Console.WriteLine($"nearn n={n0}: m-samples={N}, (m,S) cases={cases}, violations={viol}; max excess = {bestExc:E6} at {bestArg}");
    } else if (mode == "wide0") {
      // eta = log2 m exactly; c = 1 or 2 primes anywhere in [0.9 m, m] (a_p = 1), d primes just above m (a_p = 0), c + d in [n-1, n+1]
      int n0 = int.Parse(args[1]); int N = int.Parse(args[2]); int maxPrimes = args.Length > 3 ? int.Parse(args[3]) : 120; var rnd = new Random(7700 + n0); var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray();
      BigInteger center = BigInteger.One << (n0 * n0); double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0; object lk = new object();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); long u = r.Next(-(1 << 20), 1 << 20); BigInteger m = center + (center * 3 * u) / ((BigInteger)(n0 * n0) << 20);
        var below = new List<BigInteger>(); BigInteger lowB = m - m / 10; for (BigInteger q = m; q > lowB && below.Count < maxPrimes; q--) { if (IsPrime(q)) { below.Add(q); q -= r.Next(0, 3000); } }
        var above = new List<BigInteger>(); for (BigInteger q = m + 1; above.Count < 10; q++) if (IsPrime(q)) above.Add(q);
        BigInteger eta = Log2FP(m); var lb = below.Select(Log2FP).ToArray(); var la = above.Select(Log2FP).ToArray(); var ib = lb.Select(l => (F * F) / SqrtFP(l)).ToArray(); var ia = la.Select(l => (F * F) / SqrtFP(l)).ToArray();
        for (int ma = 0; ma < (1 << above.Count); ma++) {
          int d = 0; BigInteger Aa = 0; for (int i = 0; i < above.Count; i++) if ((ma >> i & 1) == 1) { d++; Aa += ia[i]; }
          for (int c = 1; c <= 2; c++) {
            if (c + d < n0 - 1 || c + d > n0 + 1) continue;
            for (int i = 0; i < below.Count; i++) for (int j = (c == 1 ? below.Count - 1 : i + 1); j < (c == 1 ? below.Count : below.Count); j++) {
              if (c == 1 && j != below.Count - 1) continue; BigInteger Ab = ib[i] + (c == 2 ? ib[j] : 0); BigInteger Dl = lb[i] + (c == 2 ? lb[j] : 0);
              BigInteger A = Ab + Aa; BigInteger A2 = (A * A) >> PREC; BigInteger aS = BigInteger.Max(F, A2); BigInteger e2 = (eta * eta) >> PREC;
              BigInteger Qt = ((e2 * A2) >> PREC) - 4 * (eta * c - Dl - eta); if (Qt < 0) Qt = 0;
              BigInteger ts = (((eta * A) >> PREC) + SqrtFP(Qt)) / 2; BigInteger t2 = (ts * ts) >> PREC; BigInteger y = t2 - eta - Dl; BigInteger M = CeilFP(y);
              BigInteger Lv = (((aS * e2) >> PREC) + ((aS * eta) >> PREC) + F - 1) / F; BigInteger e = Dl + (M << PREC) - (Lv << PREC); double ed = ToDouble(e);
              lock (lk) { cases++; if (e > 0) { viol++; if (viol <= 12) Console.WriteLine($"VIOLATION at eta=log2 m: n={n0} m={m} c={c} d={d} below=({below[i]}{(c == 2 ? "," + below[j] : "")}) ma={ma} M={M} L={Lv} excess={ed:E4}"); } if (ed > bestExc) { bestExc = ed; bestArg = $"m={m} c={c} d={d} below=({below[i]}{(c == 2 ? "," + below[j] : "")}) M={M} L={Lv}"; } }
            }
          }
        }
      });
      Console.WriteLine($"wide0 (eta = log2 m) n={n0}: m-samples={N}, (m,S) cases={cases}, violations={viol}; max excess = {bestExc:E6} at {bestArg}");
    } else if (mode == "mixed0") {
      // same family as "mixed" but the excess is evaluated at eta = log2 m exactly (no real shift)
      int n0 = int.Parse(args[1]); int N = int.Parse(args[2]); int maxC = args.Length > 3 ? int.Parse(args[3]) : 3; var rnd = new Random(9500 + n0); var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray();
      BigInteger center = BigInteger.One << (n0 * n0); double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0; object lk = new object();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); long u = r.Next(-(1 << 20), 1 << 20); BigInteger m = center + (center * 3 * u) / ((BigInteger)(n0 * n0) << 20);
        var below = new List<BigInteger>(); for (BigInteger q = m; below.Count < 6 && q > 2; q--) if (IsPrime(q)) below.Add(q);
        var above = new List<BigInteger>(); for (BigInteger q = m + 1; above.Count < 10; q++) if (IsPrime(q)) above.Add(q);
        BigInteger eta = Log2FP(m); var lb = below.Select(Log2FP).ToArray(); var la = above.Select(Log2FP).ToArray();
        var ib = lb.Select(l => (F * F) / SqrtFP(l)).ToArray(); var ia = la.Select(l => (F * F) / SqrtFP(l)).ToArray();
        for (int mb = 1; mb < (1 << below.Count); mb++) {
          int c = 0; BigInteger Ab = 0, Dl = 0; for (int i = 0; i < below.Count; i++) if ((mb >> i & 1) == 1) { c++; Ab += ib[i]; Dl += lb[i]; }
          if (c > maxC) continue;
          for (int ma = 0; ma < (1 << above.Count); ma++) {
            int d = 0; BigInteger Aa = 0; for (int i = 0; i < above.Count; i++) if ((ma >> i & 1) == 1) { d++; Aa += ia[i]; }
            if (c + d < n0 - 1 || c + d > n0 + 1) continue;
            BigInteger A = Ab + Aa; BigInteger A2 = (A * A) >> PREC; BigInteger aS = BigInteger.Max(F, A2); BigInteger e2 = (eta * eta) >> PREC;
            BigInteger Qt = ((e2 * A2) >> PREC) - 4 * (eta * c - Dl - eta); if (Qt < 0) Qt = 0;
            BigInteger ts = (((eta * A) >> PREC) + SqrtFP(Qt)) / 2; BigInteger t2 = (ts * ts) >> PREC; BigInteger y = t2 - eta - Dl; BigInteger M = CeilFP(y);
            BigInteger Lv = (((aS * e2) >> PREC) + ((aS * eta) >> PREC) + F - 1) / F; BigInteger e = Dl + (M << PREC) - (Lv << PREC); double ed = ToDouble(e);
            lock (lk) { cases++; if (e > 0) { viol++; if (viol <= 10) Console.WriteLine($"VIOLATION at eta=log2 m: n={n0} m={m} c={c} d={d} mb={mb} ma={ma} M={M} L={Lv} excess={ed:E4}"); } if (ed > bestExc) { bestExc = ed; bestArg = $"tau={ToDouble(eta) - n0 * n0:E3} c={c} d={d} M={M} L={Lv}"; } }
          }
        }
      });
      Console.WriteLine($"mixed0 (eta = log2 m) n={n0}: m-samples={N}, (m,S) cases={cases}, violations={viol}; max excess = {bestExc:E6} at {bestArg}");
    } else if (mode == "mixed") {
      // c primes just below m (a_p = 1) and d primes just above m (a_p = 0), c + d in [n-1, n+1], m in 2^(n^2) (1 +- 3/n^2); eta in [log2 m, log2 m + 0.05]
      int n0 = int.Parse(args[1]); int N = int.Parse(args[2]); int maxC = args.Length > 3 ? int.Parse(args[3]) : 3; var rnd = new Random(9000 + n0); var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray();
      BigInteger center = BigInteger.One << (n0 * n0); double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0; object lk = new object();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); long u = r.Next(-(1 << 20), 1 << 20); BigInteger m = center + (center * 3 * u) / ((BigInteger)(n0 * n0) << 20);
        var below = new List<BigInteger>(); for (BigInteger q = m; below.Count < 6 && q > 2; q--) if (IsPrime(q)) below.Add(q);
        var above = new List<BigInteger>(); for (BigInteger q = m + 1; above.Count < 10; q++) if (IsPrime(q)) above.Add(q);
        BigInteger eta0 = Log2FP(m); var lb = below.Select(Log2FP).ToArray(); var la = above.Select(Log2FP).ToArray();
        var ib = lb.Select(l => (F * F) / SqrtFP(l)).ToArray(); var ia = la.Select(l => (F * F) / SqrtFP(l)).ToArray();
        for (int mb = 1; mb < (1 << below.Count); mb++) {
          int c = 0; BigInteger Ab = 0, Dl = 0; for (int i = 0; i < below.Count; i++) if ((mb >> i & 1) == 1) { c++; Ab += ib[i]; Dl += lb[i]; }
          if (c > maxC) continue;
          for (int ma = 0; ma < (1 << above.Count); ma++) {
            int d = 0; BigInteger Aa = 0; for (int i = 0; i < above.Count; i++) if ((ma >> i & 1) == 1) { d++; Aa += ia[i]; }
            if (c + d < n0 - 1 || c + d > n0 + 1) continue;
            BigInteger e = ScanBreakpoints(Dl, c, Ab + Aa, eta0, 0.05, out string arg, out long nb); double ed = ToDouble(e);
            lock (lk) { cases++; if (e > 0) { viol++; if (viol <= 10) Console.WriteLine($"VIOLATION n={n0} m={m} c={c} d={d} mb={mb} ma={ma} {arg} excess={ed:E4}"); } if (ed > bestExc) { bestExc = ed; bestArg = $"tau={ToDouble(eta0) - n0 * n0:E3} c={c} d={d} {arg}"; } }
          }
        }
      });
      Console.WriteLine($"mixed n={n0}: m-samples={N}, (m,S) cases={cases}, violations={viol}; max excess = {bestExc:E6} at {bestArg}");
    } else if (mode == "near") {
      // a few primes just below a random large m (slack tiny, a_S = 1 for eta >= alpha^2): near b N maxSize
      int b = int.Parse(args[1]); int N = int.Parse(args[2]); int maxSize = args.Length > 3 ? int.Parse(args[3]) : 4; var rnd = new Random(1000 + b);
      var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray(); double bestExc = -1e9; string bestArg = ""; long cases = 0, viol = 0; object lk = new object();
      var tops = new List<(double ex, string arg)>();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); byte[] bytes = new byte[b / 8 + 2]; r.NextBytes(bytes); BigInteger m = (BigInteger.One << b) + (new BigInteger(bytes.Concat(new byte[]{ 0 }).ToArray()) % (BigInteger.One << b));
        var win = new List<BigInteger>(); for (BigInteger q = m; win.Count < 8 && q > 2; q--) if (IsPrime(q)) win.Add(q);
        BigInteger eta0 = Log2FP(m); int n = win.Count; var lam = win.Select(Log2FP).ToArray(); var inv = lam.Select(l => (F * F) / SqrtFP(l)).ToArray();
        for (int mask = 1; mask < (1 << n); mask++) {
          int c = 0; BigInteger A = 0, Dl = 0; for (int i = 0; i < n; i++) if ((mask >> i & 1) == 1) { c++; A += inv[i]; Dl += lam[i]; }
          if (c > maxSize) continue;
          BigInteger e = ScanBreakpoints(Dl, c, A, eta0, 0.3, out string arg, out long nb); double ed = ToDouble(e);
          lock (lk) { cases++; if (e > 0) { viol++; if (viol <= 10) Console.WriteLine($"VIOLATION b={b} m={m} c={c} mask={mask} {arg} excess={ed:E4}"); } if (ed > bestExc) { bestExc = ed; bestArg = $"m={m} c={c} mask={mask} {arg}"; } }
        }
      });
      Console.WriteLine($"near b={b}: m-samples={N}, (m,S) cases={cases}, violations={viol}; max excess = {bestExc:E6} at {bestArg}");
    } else {
      // random general sets (a_p = a_p(1/m) general), m random, all real eta in [log2 m, log2 m + 3]
      int N = args.Length > 1 ? int.Parse(args[1]) : 20000; var rnd = new Random(77); var primes = Enumerable.Range(2, 3000).Where(x => IsPrime(x)).ToArray();
      double bestExc = -1e9; string bestArg = ""; long viol = 0, tested = 0; object lk = new object(); var seeds = Enumerable.Range(0, N).Select(_ => rnd.Next()).ToArray();
      Parallel.ForEach(seeds, seed => {
        var r = new Random(seed); int sz = r.Next(1, 7); var ps = primes.OrderBy(_ => r.Next()).Take(sz).ToArray(); long m = r.Next(2, 3000000);
        var lam = ps.Select(p => Log2FP(p)).ToArray(); var a = ps.Select(p => { int aa = 0; BigInteger pw = p; while (pw <= m) { aa++; pw *= (BigInteger)p * p; } return aa; }).ToArray();
        BigInteger A = 0, Dl = 0; int al = 0; for (int i = 0; i < ps.Length; i++) { A += (F * F) / SqrtFP(lam[i]); Dl += (BigInteger)a[i] * a[i] * lam[i]; al += a[i]; }
        BigInteger e = ScanBreakpoints(Dl, al, A, Log2FP(m), 3.0, out string arg, out long nb); double ed = ToDouble(e);
        lock (lk) { tested++; if (e > 0) { viol++; if (viol <= 5) Console.WriteLine($"VIOLATION m={m} S={{{string.Join(",", ps)}}} a={{{string.Join(",", a)}}} {arg} excess={ed:E4}"); } if (ed > bestExc && !(m < 4)) { bestExc = ed; bestArg = $"m={m} S={{{string.Join(",", ps)}}} {arg}"; } }
      });
      Console.WriteLine($"random general sets: cases={tested}, violations={viol}; max excess over all real eta in [log2 m, log2 m + 3] = {bestExc:E6} at {bestArg}");
    }
  }
}
