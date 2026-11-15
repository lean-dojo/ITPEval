;; Statement-only formalization of thousand-theorems corpus artifact Q3527215,
;; "Hilbert projection theorem": every point in a real inner-product space has
;; a nearest point in each nonempty complete convex subset. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative application interfaces present arbitrary scalar and vector
;; carriers, operations, subsets, and sequences. The real scalars are encoded
;; as a Dedekind-complete ordered field. All typing, algebraic, order,
;; inner-product, convexity, and subset-completeness assumptions are explicit.
;;
;; Squared norms are used throughout. In a real inner-product space,
;; ||x|| <= ||y|| iff <x,x> <= <y,y>, so the final nearest-point condition is
;; equivalent to equality with the infimum in the Lean source.

(defstub q3527215-apply1 (function x) t)
(defstub q3527215-apply2 (function x y) t)

(defun q3527215-member-p (carrier x)
  (if (q3527215-apply1 carrier x) t nil))

;; A presentation of the real numbers as a complete ordered field.

(defun-sk q3527215-real-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q3527215-member-p carrier x)
      (q3527215-member-p carrier y)
      (q3527215-member-p carrier z))
     (let* ((xy-add (q3527215-apply2 add x y))
            (yz-add (q3527215-apply2 add y z))
            (xy-multiply (q3527215-apply2 multiply x y))
            (yz-multiply (q3527215-apply2 multiply y z))
            (negative-x (q3527215-apply1 negate x))
            (inverse-x (q3527215-apply1 inverse x)))
       (and
        (q3527215-member-p carrier xy-add)
        (q3527215-member-p carrier xy-multiply)
        (q3527215-member-p carrier negative-x)
        (q3527215-member-p carrier inverse-x)
        (equal
         (q3527215-apply2 add xy-add z)
         (q3527215-apply2 add x yz-add))
        (equal xy-add (q3527215-apply2 add y x))
        (equal (q3527215-apply2 add x zero) x)
        (equal
         (q3527215-apply2 add x negative-x)
         zero)
        (equal
         (q3527215-apply2 multiply xy-multiply z)
         (q3527215-apply2 multiply x yz-multiply))
        (equal
         xy-multiply
         (q3527215-apply2 multiply y x))
        (equal
         (q3527215-apply2 multiply x one)
         x)
        (equal
         (q3527215-apply1 inverse zero)
         zero)
        (implies
         (not (equal x zero))
         (equal
          (q3527215-apply2 multiply x inverse-x)
          one))
        (equal
         (q3527215-apply2 multiply x yz-add)
         (q3527215-apply2
          add
          (q3527215-apply2 multiply x y)
          (q3527215-apply2 multiply x z))))))))

(defun-sk q3527215-real-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q3527215-member-p carrier x)
      (q3527215-member-p carrier y)
      (q3527215-member-p carrier z))
     (and
      (not (q3527215-apply2 less x x))
      (or
       (equal x y)
       (q3527215-apply2 less x y)
       (q3527215-apply2 less y x))
      (implies
       (and
        (q3527215-apply2 less x y)
        (q3527215-apply2 less y z))
       (q3527215-apply2 less x z))
      (implies
       (q3527215-apply2 less x y)
       (q3527215-apply2
        less
        (q3527215-apply2 add x z)
        (q3527215-apply2 add y z)))
      (implies
       (and
        (q3527215-apply2 less zero x)
        (q3527215-apply2 less zero y))
       (q3527215-apply2
        less
        zero
        (q3527215-apply2 multiply x y)))))))

(defun q3527215-real-leq-p (less left right)
  (not (q3527215-apply2 less right left)))

(defun q3527215-positive-real-p
    (carrier zero less value)
  (and
   (q3527215-member-p carrier value)
   (q3527215-apply2 less zero value)))

(defun-sk q3527215-real-set-valid-p (carrier set)
  (forall (x)
    (implies
     (q3527215-apply1 set x)
     (q3527215-member-p carrier x))))

(defun-sk q3527215-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q3527215-member-p carrier x)
     (q3527215-apply1 set x))))

(defun-sk q3527215-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q3527215-member-p carrier x)
      (q3527215-apply1 set x))
     (q3527215-real-leq-p less x bound))))

(defun-sk q3527215-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q3527215-member-p carrier bound)
     (q3527215-real-upper-bound-p
      carrier less set bound))))

(defun-sk q3527215-real-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (q3527215-member-p carrier bound)
      (q3527215-real-upper-bound-p
       carrier less set bound))
     (q3527215-real-leq-p less supremum bound))))

(defun q3527215-real-supremum-p
    (carrier less set supremum)
  (and
   (q3527215-member-p carrier supremum)
   (q3527215-real-upper-bound-p
    carrier less set supremum)
   (q3527215-real-least-upper-bound-p
    carrier less set supremum)))

(defun-sk q3527215-real-supremum-exists-p
    (carrier less set)
  (exists (supremum)
    (q3527215-real-supremum-p
     carrier less set supremum)))

(defun-sk q3527215-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q3527215-real-set-valid-p carrier set)
      (q3527215-real-set-nonempty-p carrier set)
      (q3527215-real-bounded-above-p
       carrier less set))
     (q3527215-real-supremum-exists-p
      carrier less set))))

(defun q3527215-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (q3527215-member-p carrier zero)
   (q3527215-member-p carrier one)
   (not (equal zero one))
   (q3527215-apply2 less zero one)
   (q3527215-real-field-laws-p
    carrier zero one add multiply negate inverse)
   (q3527215-real-order-laws-p
    carrier zero add multiply less)
   (q3527215-real-complete-p carrier less)))

;; Real inner-product spaces. No completeness assumption is imposed on the
;; ambient vector space; the source assumes completeness only of the subset.

(defun-sk q3527215-vector-space-laws-p
    (real-carrier real-one real-add real-multiply
     space-carrier vector-zero vector-add vector-negate scalar-multiply)
  (forall (a b x y z)
    (implies
     (and
      (q3527215-member-p real-carrier a)
      (q3527215-member-p real-carrier b)
      (q3527215-member-p space-carrier x)
      (q3527215-member-p space-carrier y)
      (q3527215-member-p space-carrier z))
     (let* ((xy-add (q3527215-apply2 vector-add x y))
            (yz-add (q3527215-apply2 vector-add y z))
            (negative-x (q3527215-apply1 vector-negate x))
            (a-times-x
             (q3527215-apply2 scalar-multiply a x))
            (b-times-x
             (q3527215-apply2 scalar-multiply b x)))
       (and
        (q3527215-member-p space-carrier xy-add)
        (q3527215-member-p space-carrier negative-x)
        (q3527215-member-p space-carrier a-times-x)
        (equal
         (q3527215-apply2 vector-add xy-add z)
         (q3527215-apply2 vector-add x yz-add))
        (equal
         xy-add
         (q3527215-apply2 vector-add y x))
        (equal
         (q3527215-apply2 vector-add x vector-zero)
         x)
        (equal
         (q3527215-apply2 vector-add x negative-x)
         vector-zero)
        (equal
         (q3527215-apply2 scalar-multiply real-one x)
         x)
        (equal
         (q3527215-apply2
          scalar-multiply
          (q3527215-apply2 real-multiply a b)
          x)
         (q3527215-apply2
          scalar-multiply a b-times-x))
        (equal
         (q3527215-apply2
          scalar-multiply
          (q3527215-apply2 real-add a b)
          x)
         (q3527215-apply2
          vector-add a-times-x b-times-x))
        (equal
         (q3527215-apply2
          scalar-multiply a xy-add)
         (q3527215-apply2
          vector-add
          a-times-x
          (q3527215-apply2
           scalar-multiply a y))))))))

(defun-sk q3527215-inner-product-laws-p
    (real-carrier real-zero real-add real-multiply real-less
     space-carrier vector-zero vector-add scalar-multiply inner)
  (forall (a x y z)
    (implies
     (and
      (q3527215-member-p real-carrier a)
      (q3527215-member-p space-carrier x)
      (q3527215-member-p space-carrier y)
      (q3527215-member-p space-carrier z))
     (let ((inner-xy (q3527215-apply2 inner x y))
           (inner-xx (q3527215-apply2 inner x x)))
       (and
        (q3527215-member-p real-carrier inner-xy)
        (equal
         (q3527215-apply2
          inner
          (q3527215-apply2 vector-add x y)
          z)
         (q3527215-apply2
          real-add
          (q3527215-apply2 inner x z)
          (q3527215-apply2 inner y z)))
        (equal
         (q3527215-apply2
          inner
          (q3527215-apply2 scalar-multiply a x)
          y)
         (q3527215-apply2
          real-multiply a inner-xy))
        (equal
         inner-xy
         (q3527215-apply2 inner y x))
        (q3527215-real-leq-p
         real-less real-zero inner-xx)
        (iff
         (equal inner-xx real-zero)
         (equal x vector-zero)))))))

(defun q3527215-real-inner-product-space-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier vector-zero vector-add vector-negate
     scalar-multiply inner)
  (and
   (q3527215-real-field-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)
   (q3527215-member-p space-carrier vector-zero)
   (q3527215-vector-space-laws-p
    real-carrier real-one real-add real-multiply
    space-carrier vector-zero vector-add vector-negate
    scalar-multiply)
   (q3527215-inner-product-laws-p
    real-carrier real-zero real-add real-multiply real-less
    space-carrier vector-zero vector-add scalar-multiply inner)))

(defun q3527215-vector-subtract
    (vector-add vector-negate x y)
  (q3527215-apply2
   vector-add x (q3527215-apply1 vector-negate y)))

(defun q3527215-norm-square
    (vector-add vector-negate inner x y)
  (let ((difference
         (q3527215-vector-subtract
          vector-add vector-negate x y)))
    (q3527215-apply2 inner difference difference)))

(defun q3527215-distance-lt-p
    (real-multiply real-less vector-add vector-negate inner
     x y epsilon)
  (q3527215-apply2
   real-less
   (q3527215-norm-square
    vector-add vector-negate inner x y)
   (q3527215-apply2 real-multiply epsilon epsilon)))

;; Arbitrary subsets, convexity, and completeness in the induced norm metric.

(defun-sk q3527215-vector-set-valid-p
    (space-carrier subset)
  (forall (x)
    (implies
     (q3527215-apply1 subset x)
     (q3527215-member-p space-carrier x))))

(defun-sk q3527215-vector-set-nonempty-p
    (space-carrier subset)
  (exists (x)
    (and
     (q3527215-member-p space-carrier x)
     (q3527215-apply1 subset x))))

(defun-sk q3527215-convex-p
    (real-carrier real-zero real-one real-add real-less
     vector-add scalar-multiply subset)
  (forall (a b x y)
    (implies
     (and
      (q3527215-member-p real-carrier a)
      (q3527215-member-p real-carrier b)
      (q3527215-real-leq-p real-less real-zero a)
      (q3527215-real-leq-p real-less real-zero b)
      (equal
       (q3527215-apply2 real-add a b)
       real-one)
      (q3527215-apply1 subset x)
      (q3527215-apply1 subset y))
     (q3527215-apply1
      subset
      (q3527215-apply2
       vector-add
       (q3527215-apply2 scalar-multiply a x)
       (q3527215-apply2 scalar-multiply b y))))))

(defun-sk q3527215-subset-sequence-p (subset sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527215-apply1
      subset (q3527215-apply1 sequence n)))))

(defun-sk q3527215-cauchy-tail-p
    (real-multiply real-less vector-add vector-negate inner
     sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q3527215-distance-lt-p
      real-multiply real-less vector-add vector-negate inner
      (q3527215-apply1 sequence m)
      (q3527215-apply1 sequence n)
      epsilon))))

(defun-sk q3527215-cauchy-cutoff-exists-p
    (real-multiply real-less vector-add vector-negate inner
     sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3527215-cauchy-tail-p
      real-multiply real-less vector-add vector-negate inner
      sequence epsilon cutoff))))

(defun-sk q3527215-cauchy-sequence-p
    (real-carrier real-zero real-multiply real-less
     vector-add vector-negate inner sequence)
  (forall (epsilon)
    (implies
     (q3527215-positive-real-p
      real-carrier real-zero real-less epsilon)
     (q3527215-cauchy-cutoff-exists-p
      real-multiply real-less vector-add vector-negate inner
      sequence epsilon))))

(defun-sk q3527215-convergence-tail-p
    (real-multiply real-less vector-add vector-negate inner
     sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q3527215-distance-lt-p
      real-multiply real-less vector-add vector-negate inner
      (q3527215-apply1 sequence n)
      limit
      epsilon))))

(defun-sk q3527215-convergence-cutoff-exists-p
    (real-multiply real-less vector-add vector-negate inner
     sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3527215-convergence-tail-p
      real-multiply real-less vector-add vector-negate inner
      sequence limit epsilon cutoff))))

(defun-sk q3527215-sequence-converges-p
    (real-carrier real-zero real-multiply real-less
     vector-add vector-negate inner sequence limit)
  (forall (epsilon)
    (implies
     (q3527215-positive-real-p
      real-carrier real-zero real-less epsilon)
     (q3527215-convergence-cutoff-exists-p
      real-multiply real-less vector-add vector-negate inner
      sequence limit epsilon))))

(defun-sk q3527215-subset-limit-exists-p
    (real-carrier real-zero real-multiply real-less
     vector-add vector-negate inner subset sequence)
  (exists (limit)
    (and
     (q3527215-apply1 subset limit)
     (q3527215-sequence-converges-p
      real-carrier real-zero real-multiply real-less
      vector-add vector-negate inner sequence limit))))

(defun-sk q3527215-complete-subset-p
    (real-carrier real-zero real-multiply real-less
     vector-add vector-negate inner subset)
  (forall (sequence)
    (implies
     (and
      (q3527215-subset-sequence-p subset sequence)
      (q3527215-cauchy-sequence-p
       real-carrier real-zero real-multiply real-less
       vector-add vector-negate inner sequence))
     (q3527215-subset-limit-exists-p
      real-carrier real-zero real-multiply real-less
      vector-add vector-negate inner subset sequence))))

;; The conclusion: each ambient point has an internally existentially
;; quantified member of K whose distance is no greater than that of every
;; other member of K.

(defun-sk q3527215-nearest-point-p
    (real-less vector-add vector-negate inner subset u v)
  (forall (w)
    (implies
     (q3527215-apply1 subset w)
     (q3527215-real-leq-p
      real-less
      (q3527215-norm-square
       vector-add vector-negate inner u v)
      (q3527215-norm-square
       vector-add vector-negate inner u w)))))

(defun-sk q3527215-nearest-point-exists-p
    (real-less vector-add vector-negate inner subset u)
  (exists (v)
    (and
     (q3527215-apply1 subset v)
     (q3527215-nearest-point-p
      real-less vector-add vector-negate inner subset u v))))

(defun-sk q3527215-all-points-have-nearest-p
    (space-carrier real-less vector-add vector-negate inner subset)
  (forall (u)
    (implies
     (q3527215-member-p space-carrier u)
     (q3527215-nearest-point-exists-p
      real-less vector-add vector-negate inner subset u))))

(defun thousand-theorems-q3527215-hilbert-projection-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier vector-zero vector-add vector-negate
     scalar-multiply inner subset)
  (implies
   (and
    (q3527215-real-inner-product-space-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier vector-zero vector-add vector-negate
     scalar-multiply inner)
    (q3527215-vector-set-valid-p space-carrier subset)
    (q3527215-vector-set-nonempty-p space-carrier subset)
    (q3527215-complete-subset-p
     real-carrier real-zero real-multiply real-less
     vector-add vector-negate inner subset)
    (q3527215-convex-p
     real-carrier real-zero real-one real-add real-less
     vector-add scalar-multiply subset))
   (q3527215-all-points-have-nearest-p
    space-carrier real-less vector-add vector-negate inner subset)))

(value-triple :itpeval-statement-checked)
:q
