using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;


// record_minima: all records of k -> P_S(k) = max_q ||k/q|| by lattice enumeration with a rational radius (exact integers; Fincke-Pohst in doubles).
class P {
  // ---- integral LLL (Cohen 2.6.7), basis rows b[0..n-1], delta = 3/4
  static void Lll(BigInteger[][] b) {
    int n = b.Length; var d = new BigInteger[n + 1]; var lam = new BigInteger[n][]; for (int i = 0; i < n; i++) lam[i] = new BigInteger[n];
    d[0] = 1; d[1] = Dot(b[0], b[0]); int k = 1, kmax = 0;
    Action<int, int> red = (kk, l) => {
      if (2 * BigInteger.Abs(lam[kk][l]) > d[l + 1]) {
        BigInteger q = Round(lam[kk][l], d[l + 1]);
        for (int t = 0; t < b[kk].Length; t++) b[kk][t] -= q * b[l][t];
        lam[kk][l] -= q * d[l + 1]; for (int i = 0; i < l; i++) lam[kk][i] -= q * lam[l][i];
      }
    };
    while (k < n) {
      if (k > kmax) {
        kmax = k;
        for (int j = 0; j <= k; j++) {
          BigInteger u = Dot(b[k], b[j]);
          for (int i = 0; i < j; i++) u = (d[i + 1] * u - lam[k][i] * lam[j][i]) / d[i];
          if (j < k) lam[k][j] = u; else d[k + 1] = u;
        }
      }
      red(k, k - 1);
      if (4 * d[k + 1] * d[k - 1] < 3 * d[k] * d[k] - 4 * lam[k][k - 1] * lam[k][k - 1]) {
        // swap k, k-1
        var tmp = b[k]; b[k] = b[k - 1]; b[k - 1] = tmp;
        for (int j = 0; j < k - 1; j++) { var t = lam[k][j]; lam[k][j] = lam[k - 1][j]; lam[k - 1][j] = t; }
        BigInteger lm = lam[k][k - 1]; BigInteger B = (d[k - 1] * d[k + 1] + lm * lm) / d[k];
        for (int i = k + 1; i <= kmax; i++) { BigInteger t = lam[i][k]; lam[i][k] = (d[k + 1] * lam[i][k - 1] - lm * t) / d[k]; lam[i][k - 1] = (B * t + lm * lam[i][k]) / d[k + 1]; }
        d[k] = B; k = Math.Max(1, k - 1);
      } else {
        for (int l = k - 2; l >= 0; l--) red(k, l);
        k++;
      }
    }
  }
  static BigInteger Round(BigInteger a, BigInteger b) { // nearest integer to a/b, b > 0
    BigInteger q = BigInteger.DivRem(2 * a + b, 2 * b, out var r); if (r < 0) q -= 1; return q;
  }
  static BigInteger Dot(BigInteger[] x, BigInteger[] y) { BigInteger s = 0; for (int i = 0; i < x.Length; i++) s += x[i] * y[i]; return s; }
  // ---- Fincke-Pohst in doubles over the LLL-reduced basis (scaled to ~1 by Z)
  static long nodes, nodeCap;
  static List<long[]> Enumerate(BigInteger[][] b, BigInteger Z, double r2, out bool capped) {
    int n = b.Length, m = b[0].Length; var v = new double[n][]; for (int i = 0; i < n; i++) { v[i] = new double[m]; for (int t = 0; t < m; t++) v[i][t] = (double)(BigInteger.Divide(b[i][t] << 50, Z)) / Math.Pow(2, 50); }
    var mu = new double[n][]; var bs = new double[n][]; var nb = new double[n]; for (int i = 0; i < n; i++) { mu[i] = new double[n]; bs[i] = (double[])v[i].Clone(); for (int j = 0; j < i; j++) { double dot = 0; for (int t = 0; t < m; t++) dot += v[i][t] * bs[j][t]; mu[i][j] = dot / nb[j]; for (int t = 0; t < m; t++) bs[i][t] -= mu[i][j] * bs[j][t]; } double s = 0; for (int t = 0; t < m; t++) s += bs[i][t] * bs[i][t]; nb[i] = s; }
    var res = new List<long[]>(); var z = new long[n]; nodes = 0; bool cap = false;
    void Rec(int i, double rem) {
      if (cap) return; nodes++; if (nodes > nodeCap) { cap = true; return; }
      double c = 0; for (int j = i + 1; j < n; j++) c += mu[j][i] * z[j]; // centre = -c
      double rad = Math.Sqrt(Math.Max(0, rem / nb[i])); long lo = (long)Math.Ceiling(-c - rad - 1e-9), hi = (long)Math.Floor(-c + rad + 1e-9);
      for (long zi = lo; zi <= hi; zi++) { z[i] = zi; double dd = (zi + c); double rem2 = rem - dd * dd * nb[i]; if (rem2 < -1e-9) continue; if (i == 0) { bool okb = true; for (int t = 0; t < m && okb; t++) { double sum = 0; for (int jj = 0; jj < n; jj++) sum += z[jj] * v[jj][t]; if (Math.Abs(sum) > 1 + 1e-7) okb = false; } if (okb) res.Add((long[])z.Clone()); } else Rec(i - 1, rem2); }
      z[i] = 0;
    }
    Rec(n - 1, r2); capped = cap; return res;
  }
  // ================= record structure of P_S (rational radius) =================
  // delta = A / Bd (Bd > 0). x is a ball element iff for every q = p^(n^2): Bd * min(x mod q, q - x mod q) < A * q.
  static BigInteger A, Bd;
  static BigInteger Pow(int p, int e) => BigInteger.Pow(p, e);
  static BigInteger CeilDiv(BigInteger x, BigInteger y) => (x + y - 1) / y;
  static int Forced(int p) { int a = 0; while (!(Bd < A * Pow(p, 2 * a + 1))) a++; return a; }   // least a with p^-(2a+1) < delta
  static BigInteger DOf(int[] S, int[] a) { BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= Pow(S[i], a[i] * a[i]); return D; }
  static List<BigInteger> Coords(int[] S, int[] a, BigInteger bound, BigInteger m) { var qs = new List<BigInteger>(); for (int i = 0; i < S.Length; i++) for (int n = a[i] + 1; ; n++) { var q = Pow(S[i], n * n); if (q > bound * m) break; qs.Add(q); } return qs; }
  // exact counting bound (Theorem 3.5): c* = least c with C(c) <= c, N0 = m^c*
  static BigInteger CountBound(int[] S, int[] a, BigInteger D, BigInteger m, out int cstar) {
    int c = 0; for (int it = 0; it < 100000; it++) { int C = Coords(S, a, D * BigInteger.Pow(m, c), m).Count; if (C <= c) { cstar = c; return BigInteger.Pow(m, c); } c = C; if (c > 4000) break; } cstar = c; return BigInteger.Pow(m, c);
  }
  static BigInteger[][] InitOrig(BigInteger D, List<BigInteger> qs) { int c = qs.Count; var o = new BigInteger[c + 1][]; o[0] = new BigInteger[c + 1]; o[0][0] = 1; for (int i = 0; i < c; i++) o[0][i + 1] = D; for (int i = 0; i < c; i++) { o[i + 1] = new BigInteger[c + 1]; o[i + 1][i + 1] = qs[i]; } return o; }
  static BigInteger[][] ScaledBasis(BigInteger[][] o, List<BigInteger> qs, BigInteger Bc, BigInteger Lq) { int c = qs.Count; var b = new BigInteger[c + 1][]; for (int r = 0; r <= c; r++) { b[r] = new BigInteger[c + 1]; b[r][0] = o[r][0] * Lq * A; for (int i = 0; i < c; i++) b[r][i + 1] = o[r][i + 1] * Bd * Bc * (Lq / qs[i]); } return b; }
  static BigInteger[][] Unscale(BigInteger[][] b, List<BigInteger> qs, BigInteger Bc, BigInteger Lq) { int c = qs.Count; var o = new BigInteger[c + 1][]; for (int r = 0; r <= c; r++) { o[r] = new BigInteger[c + 1]; o[r][0] = b[r][0] / (Lq * A); for (int i = 0; i < c; i++) o[r][i + 1] = b[r][i + 1] / (Bd * Bc * (Lq / qs[i])); } return o; }
  // least s >= 1 (s >= lbS) with all Bd |D s - j q| < A q (q in qs), s <= Smax; returns 0 if none or capped before a solution
  static BigInteger LeastS(BigInteger D, List<BigInteger> qs, BigInteger Smax, BigInteger lbS, out long totalNodes, out bool capped) {
    totalNodes = 0; capped = false; int c = qs.Count; if (c == 0) return BigInteger.Max(1, lbS);
    BigInteger Lq = 1; foreach (var q in qs) Lq = Lq / BigInteger.GreatestCommonDivisor(Lq, q) * q; var cur = InitOrig(D, qs); BigInteger ALq = A * Lq;
    for (BigInteger B = BigInteger.Max(1, lbS); ; B = B * 2) {
      if (B > Smax * 2) return 0; BigInteger Bc = BigInteger.Min(B, Smax); BigInteger Z = ALq * Bc / A * 1; Z = A * Bc * Lq;
      var basis = ScaledBasis(cur, qs, Bc, Lq); Lll(basis); cur = Unscale(basis, qs, Bc, Lq);
      var sols = Enumerate(basis, Z, (c + 1) * (1.0 + 1e-6), out bool cp); totalNodes += nodes; if (cp) capped = true;
      BigInteger best = 0;
      foreach (var zz in sols) {
        var vec = new BigInteger[c + 1]; for (int i = 0; i <= c; i++) { BigInteger s = 0; for (int t = 0; t < c + 1; t++) s += zz[t] * basis[t][i]; vec[i] = s; }
        bool ok = true; for (int i = 1; i <= c && ok; i++) if (BigInteger.Abs(vec[i]) >= Z) ok = false; if (!ok) continue;
        BigInteger sv = BigInteger.Abs(vec[0]); if (sv.IsZero) continue; if (sv % ALq != 0) continue; BigInteger s0 = sv / ALq; if (s0 > Bc || s0 < lbS) continue;
        bool ok2 = true; BigInteger x = D * s0; foreach (var q in qs) { BigInteger rm = x % q; BigInteger dist = BigInteger.Min(rm, q - rm); if (dist * Bd >= A * q) { ok2 = false; break; } }
        if (!ok2) continue; if (best.IsZero || s0 < best) best = s0;
      }
      if (!best.IsZero) return best; if (capped) return 0; if (Bc == Smax) return 0;
    }
  }
  // exact P_S(k) = max over q = p^(n^2) of min(k mod q, q - k mod q)/q, as a reduced fraction
  static (BigInteger, BigInteger) PS(int[] S, BigInteger k) {
    BigInteger bn = 0, bd = 1;
    foreach (int p in S) for (int n = 1; ; n++) { BigInteger q = Pow(p, n * n); BigInteger r = k % q; BigInteger dist = BigInteger.Min(r, q - r); if (dist * bd > bn * q) { bn = dist; bd = q; } if (q > 2 * k) break; }
    BigInteger g = BigInteger.GreatestCommonDivisor(bn, bd); if (!g.IsZero) { bn /= g; bd /= g; } return (bn, bd);
  }
  // modulus q = p^(n^2) attaining P_S(k) (first one found) with p, n and the centred residue of k mod q; valuations of k
  static string ArgInfo(int[] S, BigInteger k, BigInteger bn, BigInteger bd) {
    foreach (int p in S) for (int n = 1; ; n++) { BigInteger q = Pow(p, n * n); BigInteger r = k % q; BigInteger dist = BigInteger.Min(r, q - r); if (dist * bd == bn * q) { BigInteger cr = (2 * r < q) ? r : r - q; return $"arg={p}^{n * n} p={p} n={n} res={cr}"; } if (q > 2 * k) break; }
    return "arg=none";
  }
  static string Vals(int[] S, BigInteger k) { var v = new List<string>(); foreach (int p in S) { int e = 0; BigInteger t = k; while (!t.IsZero && t % p == 0) { t /= p; e++; } v.Add(e.ToString()); } return string.Join(",", v); }
  static double Log2B(BigInteger x) { if (x.Sign <= 0) return double.NegativeInfinity; int sh = Math.Max(0, (int)x.GetBitLength() - 60); return sh + Math.Log2((double)(x >> sh)); }
  static void Main(string[] args) {
    int[] S = args[0].Split(',').Select(int.Parse).ToArray(); int maxBits = int.Parse(args[1]); nodeCap = args.Length > 2 ? long.Parse(args[2]) : 200000000L;
    string Sname = "{" + string.Join(",", S) + "}"; var sw0 = Stopwatch.StartNew();
    BigInteger k = 1; int j = 1;
    if (args.Length > 3 && args[3].StartsWith("resume=")) { var rp = args[3].Substring(7).Split(':'); j = int.Parse(rp[0]); k = BigInteger.Parse(rp[1]); }   // resume=<j>:<k_j>
    var (num, den) = PS(S, k);
    Console.WriteLine($"S={Sname} j={j} u={k} bits={Log2B(k):F2} delta_j={num}/{den} ell_j={Log2B(den) - Log2B(num):F4} (start)");
    double[] lg = S.Select(p => Math.Log2(p)).ToArray(); double gA = lg.Sum(l => Math.Sqrt(1.0 / l)); double aS = Math.Max(1.0, gA * gA);
    int exitCode = 0;
    while (k.GetBitLength() < maxBits) {
      var sw = Stopwatch.StartNew(); A = num; Bd = den;                              // radius delta_j = P_S(k_j)
      int[] a = S.Select(p => Forced(p)).ToArray(); BigInteger D = DOf(S, a); BigInteger m = CeilDiv(Bd, A);
      BigInteger N0 = CountBound(S, a, D, m, out int cstar); var qs = Coords(S, a, D * N0, m);
      BigInteger lb = CeilDiv(k + 1, D); BigInteger s = LeastS(D, qs, N0, lb, out long nd, out bool capped);
      if (s.IsZero) { Console.WriteLine($"S={Sname} list incomplete after j={j} u={k} (search capped={capped}, coordinates={qs.Count}, nodes={nd}) [{sw.Elapsed.TotalSeconds:F1}s]"); exitCode = 2; break; }
      BigInteger kn = D * s; var (n2, d2) = PS(S, kn);
      bool strict = n2 * den < num * d2;                                             // P_S(k_{j+1}) < delta_j
      // bounds at delta_right = delta_j (u_S(delta_j) = k_{j+1}), m = ceil(1/delta_j), real eta = log2 m
      double eta = Log2B(m); double alpha = a.Sum(), Delta = 0; for (int i = 0; i < S.Length; i++) Delta += (double)a[i] * a[i] * lg[i];
      double Q = eta * eta * gA * gA - 4 * (eta * alpha - Delta - eta); double t = (eta * gA + Math.Sqrt(Math.Max(0, Q))) / 2; double M = Math.Max(0, Math.Ceiling(t * t - eta - Delta));
      double L = Math.Ceiling(aS * eta * eta + aS * eta); double lDm = Log2B(D) + cstar * eta; double ellR = Log2B(den) - Log2B(num); double lu = Log2B(kn);
      string argInfo = ArgInfo(S, kn, n2, d2), vals = Vals(S, kn), aPrev = string.Join(",", a); BigInteger sA = A, sB = Bd; A = n2; Bd = d2; string aCur = string.Join(",", S.Select(p => Forced(p))); A = sA; Bd = sB;
      j++; k = kn; (num, den) = (n2, d2);
      Console.WriteLine($"S={Sname} j={j} u={k} bits={lu:F2} delta_j={num}/{den} ell_j={Log2B(den) - Log2B(num):F4} | at delta_{{j-1}}: ell={ellR:F4} m={m} Delta={Delta:F2} cstar={cstar} log2(Dm^c*)={lDm:F2} log2(D2^M)={Delta + M:F2} L={L:F0} coords={qs.Count} nodes={nd} strict={(strict ? 1 : 0)} | {argInfo} v=({vals}) a_prev=({aPrev}) a_cur=({aCur}) [{sw.Elapsed.TotalSeconds:F1}s]");
      if (!strict) { Console.WriteLine("ERROR: P_S(k_{j}) is not below delta_{j-1}"); exitCode = 3; break; }
    }
    Console.WriteLine($"S={Sname} done: {j} records, last u has {k.GetBitLength()} bits, exit={exitCode} [{sw0.Elapsed.TotalSeconds:F1}s]");
  }
}
