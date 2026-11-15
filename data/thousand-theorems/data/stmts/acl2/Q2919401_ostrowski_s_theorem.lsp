;; Statement-only formalization of thousand-theorems corpus artifact Q2919401,
;; "Ostrowski's theorem": every nontrivial real-valued absolute value on the
;; rationals is equivalent either to the standard absolute value or, for a
;; unique prime, to the corresponding p-adic absolute value. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; An Archimedean ordered-field presentation is used for the real codomain.
;; This is bidirectionally equivalent here: every such field order-embeds in
;; R, every real-valued absolute value is an instance, and the conclusion
;; depends only on the induced order on Q.  The valuation itself remains an
;; arbitrary function on all rationals.  Equivalence is encoded exactly as in
;; AbsoluteValue.IsEquiv: equality of the two induced orders on Q.

(defstub q2919401-r-member-p (real value) t)
(defstub q2919401-r-zero (real) t)
(defstub q2919401-r-one (real) t)
(defstub q2919401-r-add (real left right) t)
(defstub q2919401-r-multiply (real left right) t)
(defstub q2919401-r-negate (real value) t)
(defstub q2919401-r-inverse (real value) t)
(defstub q2919401-r-less (real left right) t)

(defstub q2919401-absolute-value (valuation rational) t)

(defun q2919401-r-leq (real left right)
  (not (q2919401-r-less real right left)))

(defun-sk q2919401-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2919401-r-member-p real x)
      (q2919401-r-member-p real y)
      (q2919401-r-member-p real z))
     (let* ((zero (q2919401-r-zero real))
            (one (q2919401-r-one real))
            (xy-add (q2919401-r-add real x y))
            (yz-add (q2919401-r-add real y z))
            (xy-mul (q2919401-r-multiply real x y))
            (yz-mul (q2919401-r-multiply real y z))
            (neg-x (q2919401-r-negate real x))
            (inv-x (q2919401-r-inverse real x)))
       (and
        (q2919401-r-member-p real xy-add)
        (q2919401-r-member-p real xy-mul)
        (q2919401-r-member-p real neg-x)
        (q2919401-r-member-p real inv-x)
        (equal
         (q2919401-r-add real xy-add z)
         (q2919401-r-add real x yz-add))
        (equal xy-add (q2919401-r-add real y x))
        (equal (q2919401-r-add real x zero) x)
        (equal (q2919401-r-add real x neg-x) zero)
        (equal
         (q2919401-r-multiply real xy-mul z)
         (q2919401-r-multiply real x yz-mul))
        (equal xy-mul (q2919401-r-multiply real y x))
        (equal (q2919401-r-multiply real x one) x)
        (equal (q2919401-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2919401-r-multiply real x inv-x)
          one))
        (equal
         (q2919401-r-multiply
          real x (q2919401-r-add real y z))
         (q2919401-r-add
          real
          (q2919401-r-multiply real x y)
          (q2919401-r-multiply real x z))))))))

(defun-sk q2919401-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2919401-r-member-p real x)
      (q2919401-r-member-p real y)
      (q2919401-r-member-p real z))
     (let ((zero (q2919401-r-zero real)))
       (and
        (not (q2919401-r-less real x x))
        (or
         (equal x y)
         (q2919401-r-less real x y)
         (q2919401-r-less real y x))
        (implies
         (and
          (q2919401-r-less real x y)
          (q2919401-r-less real y z))
         (q2919401-r-less real x z))
        (implies
         (q2919401-r-less real x y)
         (q2919401-r-less
          real
          (q2919401-r-add real x z)
          (q2919401-r-add real y z)))
        (implies
         (and
          (q2919401-r-less real zero x)
          (q2919401-r-less real zero y))
         (q2919401-r-less
          real zero
          (q2919401-r-multiply real x y))))))))

(defun q2919401-r-nat (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2919401-r-zero real)
    (q2919401-r-add
     real
     (q2919401-r-one real)
     (q2919401-r-nat real (1- n)))))

(defun-sk q2919401-archimedean-bound-exists-p (real value)
  (exists (n)
    (and
     (natp n)
     (q2919401-r-less
      real value (q2919401-r-nat real n)))))

(defun-sk q2919401-r-archimedean-p (real)
  (forall (value)
    (implies
     (q2919401-r-member-p real value)
     (q2919401-archimedean-bound-exists-p real value))))

(defun q2919401-real-field-p (real)
  (let ((zero (q2919401-r-zero real))
        (one (q2919401-r-one real)))
    (and
     (q2919401-r-member-p real zero)
     (q2919401-r-member-p real one)
     (not (equal zero one))
     (q2919401-r-field-laws-p real)
     (q2919401-r-order-laws-p real)
     (q2919401-r-less real zero one)
     (q2919401-r-archimedean-p real))))

;; The hypotheses defining an AbsoluteValue Q R.

(defun-sk q2919401-absolute-value-laws-p (real valuation)
  (forall (q r)
    (implies
     (and (rationalp q) (rationalp r))
     (let* ((zero (q2919401-r-zero real))
            (one (q2919401-r-one real))
            (fq (q2919401-absolute-value valuation q))
            (fr (q2919401-absolute-value valuation r)))
       (and
        (q2919401-r-member-p real fq)
        (q2919401-r-member-p real fr)
        (q2919401-r-leq real zero fq)
        (iff (equal fq zero) (equal q 0))
        (implies (equal q 1) (equal fq one))
        (equal
         (q2919401-absolute-value valuation (* q r))
         (q2919401-r-multiply real fq fr))
        (q2919401-r-leq
         real
         (q2919401-absolute-value valuation (+ q r))
         (q2919401-r-add real fq fr)))))))

(defun q2919401-absolute-value-p (real valuation)
  (q2919401-absolute-value-laws-p real valuation))

(defun-sk q2919401-nontrivial-absolute-value-p (real valuation)
  (exists (q)
    (and
     (rationalp q)
     (not (equal q 0))
     (not
      (equal
       (q2919401-absolute-value valuation q)
       (q2919401-r-one real))))))

;; Primality and the exact order induced by the p-adic norm.  For nonzero
;; rationals x and y, |x|_p <= |y|_p exactly when v_p(x) >= v_p(y).
;; The latter comparison is expressed without bounding the valuation:
;; every power of p dividing the cross-product for y also divides the
;; cross-product for x.

(defun-sk q2919401-prime-factor-law-p (p)
  (forall (d)
    (implies
     (and
      (natp d)
      (< 0 d)
      (equal (mod p d) 0))
     (or (equal d 1) (equal d p)))))

(defun q2919401-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (q2919401-prime-factor-law-p p)))

(defun-sk q2919401-valuation-geq-p (p a b)
  (forall (k)
    (implies
     (natp k)
     (implies
      (equal (mod b (expt p k)) 0)
      (equal (mod a (expt p k)) 0)))))

(defun q2919401-padic-leq-p (p x y)
  (if (equal x 0)
      t
    (if (equal y 0)
        nil
      (q2919401-valuation-geq-p
       p
       (*
        (abs (numerator x))
        (denominator y))
       (*
        (abs (numerator y))
        (denominator x))))))

;; The two alternatives in Ostrowski's theorem.

(defun-sk q2919401-equivalent-to-standard-p (real valuation)
  (forall (x y)
    (implies
     (and (rationalp x) (rationalp y))
     (iff
      (q2919401-r-leq
       real
       (q2919401-absolute-value valuation x)
       (q2919401-absolute-value valuation y))
      (<= (abs x) (abs y))))))

(defun-sk q2919401-equivalent-to-padic-p (real valuation p)
  (forall (x y)
    (implies
     (and (rationalp x) (rationalp y))
     (iff
      (q2919401-r-leq
       real
       (q2919401-absolute-value valuation x)
       (q2919401-absolute-value valuation y))
      (q2919401-padic-leq-p p x y)))))

(defun-sk q2919401-padic-prime-unique-p (real valuation p)
  (forall (q)
    (implies
     (and
      (q2919401-prime-p q)
      (q2919401-equivalent-to-padic-p real valuation q))
     (equal q p))))

(defun-sk q2919401-unique-padic-prime-exists-p (real valuation)
  (exists (p)
    (and
     (q2919401-prime-p p)
     (q2919401-equivalent-to-padic-p real valuation p)
     (q2919401-padic-prime-unique-p real valuation p))))

;; Rat.AbsoluteValue.equiv_real_or_padic
(defun-sk thousand-theorems-q2919401-ostrowski-theorem-statement ()
  (forall (real valuation)
    (implies
     (and
      (q2919401-real-field-p real)
      (q2919401-absolute-value-p real valuation)
      (q2919401-nontrivial-absolute-value-p real valuation))
     (or
      (q2919401-equivalent-to-standard-p real valuation)
      (q2919401-unique-padic-prime-exists-p real valuation)))))

(value-triple :itpeval-statement-checked)
:q
