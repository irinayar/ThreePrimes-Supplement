using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;

// Exact least element u_S(1/R) by lattice enumeration.  x = D s (D = forced divisor).  For the coordinates q = p^(n^2), n > a_p, q <= R D Smax (Smax from the exact counting bound, Theorem 3.2):
// |D s - j q| R < q.  Lattice of (s, D s - j_i q_i); LLL (exact, integral) + Fincke-Pohst in doubles, every candidate verified in exact integers.
class P {
  static BigInteger Pow(int p, int e) => BigInteger.Pow(p, e);
  static int Forced(int p, int R) { int a = 0; while (Pow(p, 2 * a + 1) <= R) a++; return a; }
  static BigInteger DOf(int[] S, int[] a) { BigInteger D = 1; for (int i = 0; i < S.Length; i++) D *= Pow(S[i], a[i] * a[i]); return D; }
  static List<BigInteger> Coords(int[] S, int[] a, BigInteger bound, int R) { var qs = new List<BigInteger>(); for (int i = 0; i < S.Length; i++) for (int n = a[i] + 1; ; n++) { var q = Pow(S[i], n * n); if (q > bound * R) break; qs.Add(q); } return qs; }
  // exact counting bound: least N0 with m^{|C(N0)|} <= N0 (uniform count)
  static BigInteger CountBound(int[] S, int[] a, BigInteger D, int R) {
    BigInteger N = 1; for (int it = 0; it < 100000; it++) { var C = Coords(S, a, D * N, R).Count; BigInteger P2 = BigInteger.Pow(R, C); if (P2 <= N) return N; N = P2; if (N.GetBitLength() > 4000) return N; } return N;
  }
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
      for (long zi = lo; zi <= hi; zi++) { z[i] = zi; double dd = (zi + c); double rem2 = rem - dd * dd * nb[i]; if (rem2 < -1e-9) continue; if (i == 0) { res.Add((long[])z.Clone()); } else Rec(i - 1, rem2); }
      z[i] = 0;
    }
    Rec(n - 1, r2); capped = cap; return res;
  }
  // least s >= 1 with all |D s - j q| R < q  (q in qs), s <= Smax; returns 0 if none
  static BigInteger LeastS(BigInteger D, List<BigInteger> qs, int R, BigInteger Smax, out long totalNodes, out bool capped) {
    totalNodes = 0; capped = false; int c = qs.Count; if (c == 0) return 1;
    BigInteger Lq = 1; foreach (var q in qs) Lq = Lq / BigInteger.GreatestCommonDivisor(Lq, q) * q;
    for (BigInteger B = 1; ; B = B * 2) {
      if (B > Smax * 2) return 0; BigInteger Bc = BigInteger.Min(B, Smax); BigInteger Z = Bc * Lq;
      var basis = new BigInteger[c + 1][]; basis[0] = new BigInteger[c + 1]; basis[0][0] = Lq; for (int i = 0; i < c; i++) basis[0][i + 1] = D * R * Bc * (Lq / qs[i]);
      for (int i = 0; i < c; i++) { basis[i + 1] = new BigInteger[c + 1]; basis[i + 1][i + 1] = R * Bc * Lq; }
      Lll(basis);
      var sols = Enumerate(basis, Z, (c + 1) * (1.0 + 1e-6), out bool cp); totalNodes += nodes; if (cp) capped = true;
      BigInteger best = 0;
      foreach (var zz in sols) {
        var vec = new BigInteger[c + 1]; for (int i = 0; i <= c; i++) { BigInteger s = 0; for (int t = 0; t < c + 1; t++) s += zz[t] * basis[t][i]; vec[i] = s; }
        bool ok = true; for (int i = 1; i <= c && ok; i++) if (BigInteger.Abs(vec[i]) >= Z) ok = false; if (!ok) continue;
        BigInteger sv = BigInteger.Abs(vec[0]); if (sv.IsZero) continue; if (sv % Lq != 0) continue; BigInteger s0 = sv / Lq; if (s0 > Bc) continue;
        // exact verification with the definition
        bool ok2 = true; BigInteger x = D * s0; foreach (var q in qs) { BigInteger rm = x % q; BigInteger dist = BigInteger.Min(rm, q - rm); if (dist * R >= q) { ok2 = false; break; } }
        if (!ok2) continue; if (best.IsZero || s0 < best) best = s0;
      }
      if (!best.IsZero) return best; if (capped) return 0; if (Bc == Smax) return 0;
    }
  }
  // all valid s <= Bc (sorted), exact
  static List<BigInteger> Solutions(BigInteger D, List<BigInteger> qs, int R, BigInteger Bc, out bool capped, ref long totalNodes) {
    int c = qs.Count; capped = false; var outl = new List<BigInteger>(); BigInteger Lq = 1; foreach (var q in qs) Lq = Lq / BigInteger.GreatestCommonDivisor(Lq, q) * q; BigInteger Z = Bc * Lq;
    var basis = new BigInteger[c + 1][]; basis[0] = new BigInteger[c + 1]; basis[0][0] = Lq; for (int i = 0; i < c; i++) basis[0][i + 1] = D * R * Bc * (Lq / qs[i]);
    for (int i = 0; i < c; i++) { basis[i + 1] = new BigInteger[c + 1]; basis[i + 1][i + 1] = R * Bc * Lq; }
    Lll(basis); var sols = Enumerate(basis, Z, (c + 1) * (1.0 + 1e-6), out bool cp); totalNodes += nodes; capped = cp;
    foreach (var zz in sols) { var vec = new BigInteger[c + 1]; for (int i = 0; i <= c; i++) { BigInteger s = 0; for (int t = 0; t < c + 1; t++) s += zz[t] * basis[t][i]; vec[i] = s; }
      BigInteger sv = BigInteger.Abs(vec[0]); if (sv.IsZero || sv % Lq != 0) continue; BigInteger s0 = sv / Lq; if (s0 > Bc) continue; bool ok2 = true; BigInteger x = D * s0; foreach (var q in qs) { BigInteger rm = x % q; BigInteger dist = BigInteger.Min(rm, q - rm); if (dist * R >= q) { ok2 = false; break; } } if (ok2) outl.Add(s0); }
    outl = outl.Distinct().ToList(); outl.Sort(); return outl;
  }
  static BigInteger Cen(BigInteger x, BigInteger q) { BigInteger r = x % q; if (r < 0) r += q; return 2 * r < q ? r : r - q; }
  static double LogB(BigInteger x) { if (x.IsZero) return double.NegativeInfinity; int sh = Math.Max(0, (int)x.GetBitLength() - 60); return sh + Math.Log2((double)(x >> sh)); }
  static void Main(string[] args) {
    int[] S = args[0].Split(',').Select(int.Parse).ToArray(); int k0 = int.Parse(args[1]), k1 = int.Parse(args[2]); nodeCap = 200000000L; int[] rs = args[3].Split(',').Select(int.Parse).ToArray();
    foreach (int R in Enumerable.Range(k0, k1 - k0 + 1)) {
      var sw = Stopwatch.StartNew(); var a = S.Select(p => Forced(p, R)).ToArray(); BigInteger D = DOf(S, a); BigInteger N0 = CountBound(S, a, D, R);
      var qs = Coords(S, a, D * N0, R); BigInteger s1 = LeastS(D, qs, R, N0, out long nd, out bool capped); if (s1.IsZero) { Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{R}: not found"); continue; }
      // version 13: the coordinate list is rebuilt for every search bound Bn (all moduli q <= m D Bn), since a bound N0 for the FIRST element is not a bound for the second vector;
      // w1 are the centred residues of D s1 modulo the current list. Capped steps are reported (cap1 for u, cap2 for the list that gave T2).
      // list ball elements with s <= B, doubling B until an independent vector and an element prime to every r exist
      BigInteger Bn = s1 * 2; List<BigInteger> lst = null; BigInteger T2 = 0; int rank2 = 0; var Nr = new BigInteger[rs.Length]; var rankR = new int[rs.Length]; long ndl = 0; bool cap2 = false;
      var qB = qs; BigInteger[] w1 = null;
      for (int tries = 0; tries < 300; tries++) {
        qB = Coords(S, a, D * Bn, R); w1 = qB.Select(q => Cen(D * s1, q)).ToArray();
        lst = Solutions(D, qB, R, Bn, out bool cp, ref ndl); T2 = 0; cap2 = cp;
        for (int i = 0; i < lst.Count; i++) { var s = lst[i]; bool prop = false; if (s % s1 == 0) { var aa = s / s1; prop = true; for (int t = 0; t < qB.Count && prop; t++) if (Cen(D * s, qB[t]) != aa * w1[t]) prop = false; } if (!prop) { T2 = s; rank2 = i + 1; break; } }
        for (int j = 0; j < rs.Length; j++) { int idx = lst.FindIndex(z => z % rs[j] != 0); if (idx >= 0) { Nr[j] = lst[idx]; rankR[j] = idx + 1; } }
        if (!T2.IsZero && Nr.All(x => !x.IsZero)) break; if (cp || lst.Count > 2000000 || Bn.GetBitLength() > s1.GetBitLength() + 300) break; Bn *= 2;
      }
      qs = qB;
      if (T2.IsZero) { Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{R}: u={D * s1} cap1={(capped ? 1 : 0)} T2 not found within the bound (cap2={(cap2 ? 1 : 0)})"); continue; }
      // quantities of the argument at scale T = T2: retained coordinates q <= m D T, mu = max(s1/T, max m|w_i|/q_i)
      int c2 = qs.Count(q => q < R * D * T2); double nu = 0; for (int t = 0; t < qs.Count; t++) if (qs[t] < R * D * T2) nu = Math.Max(nu, (double)R * Math.Abs((double)w1[t]) / (double)qs[t]); double mu = Math.Max(Math.Exp(LogB(s1) * Math.Log(2) - LogB(T2) * Math.Log(2)), nu);
      var w2 = qs.Select(q => Cen(D * T2, q)).ToArray(); double nu2 = 0; for (int t = 0; t < qs.Count; t++) if (qs[t] < R * D * T2) nu2 = Math.Max(nu2, (double)R * Math.Abs((double)w2[t]) / (double)qs[t]);
      double lB2 = c2 * Math.Log2(R) - Math.Log2(mu) - c2 * Math.Log2(1 - mu / 2); double lT2 = LogB(T2);
      string extra = ""; for (int j = 0; j < rs.Length; j++) extra += $" | r={rs[j]}: N/D={Nr[j]} rank={rankR[j]} N==T2:{(Nr[j] == T2 ? 1 : 0)} r|s1:{(s1 % rs[j] == 0 ? 1 : 0)} r|T2:{(T2 % rs[j] == 0 ? 1 : 0)}";
      Console.WriteLine($"S={{{string.Join(",", S)}}} delta=1/{R}: u={D * s1}  s1={s1} log2s1={LogB(s1):F2} nu1={nu:F4} mu={mu:F4} c2={c2} T2={T2} log2T2={lT2:F2} rank2={rank2} nu2={nu2:F4} log2B2={lB2:F2} T2<=B2:{(lT2 <= lB2 + 1e-9 ? 1 : 0)} log2(B2/T2)={lB2 - lT2:F2} cap1={(capped ? 1 : 0)} cap2={(cap2 ? 1 : 0)}{extra} [{sw.Elapsed.TotalSeconds:F1}s]");
    }
  }
}
