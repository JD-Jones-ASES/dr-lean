import DR.Endpoint.NearEndpointCutCertificates

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

example : NearEndpointBracketCertificate 21 := nearEndpointBracketCertificate21
example : NearEndpointBracketCertificate 25 := nearEndpointBracketCertificate25

-- The exact rational bracket separates opposite signs at adjacent10^−8 points.
example : nearEndpointRootLeft 21=4976889/100000000 ∧
    nearEndpointRootRight 21=4976890/100000000 ∧
    nearEndpointCubicRat 20 (nearEndpointRootLeft 21)<0 ∧
    0<nearEndpointCubicRat 20 (nearEndpointRootRight 21) := by decide +kernel

-- Reversing the bracket sign and extending the literal table out of range are rejected.
example : ¬(nearEndpointCubicRat 20 (nearEndpointRootRight 21)<0) := by decide +kernel
example : ¬NearEndpointBracketCertificate 26 := by decide +kernel

-- Both axis orientations are checked, as well as a mixed one-grid-step cut.
example : NearEndpointCutCertificate 21 1 21 ∧ NearEndpointCutCertificate 21 21 1 ∧
    NearEndpointCutCertificate 21 11 11 := by
  exact ⟨nearEndpointCutCertificate21 1 21,nearEndpointCutCertificate21 21 1,
    nearEndpointCutCertificate21 11 11⟩

-- Dropping the two-zero improvement makes even the axis comparison fail.
example : let a:=nearEndpointAvoidanceRat 21
    ¬(a-a-(20 : ℚ)^2*nearEndpointCutRat 21 21 1*a^2/(4*(1-a))>3*a/10000) := by
  decide +kernel

-- Complete ordered coverage is1380; omitting one admitted pair changes a dimension's count.
example : (∑ n ∈ Finset.Icc 21 25,
    ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun kl =>
      n<kl.1+kl.2 ∧ (kl.1≠n ∨ kl.2≠n)).card)=1380 := nearEndpoint_finite_cut_coverage

example : let S := (Finset.range 22 ×ˢ Finset.range 22).filter fun kl =>
    21<kl.1+kl.2 ∧ (kl.1≠21 ∨ kl.2≠21)
    S.card=230 ∧ (S.erase (1,21)).card=229 := by decide +kernel

example {n k l : ℕ} (hn : 21≤n) (hn' : n≤25) (hk : k≤n) (hl : l≤n)
    (hp : n<k+l) (hw : k≠n ∨ l≠n) :
    nearEndpointSizedCutCoefficient n k l*distinctUniformProbability n (n-1)/
      (1-distinctUniformProbability n (n-1))<1/10000 :=
  (nearEndpointCut_real_certificate hn hn' hk hl hp hw).1

#print axioms nearEndpointBracketCertificate_checked
#print axioms nearEndpointCutCertificate_checked
#print axioms nearEndpoint_finite_cut_coverage
#print axioms nearEndpointCut_real_certificate
#print axioms nearEndpointPermanentFloorRat_gt_boundary
end DittertRybin.Tests
