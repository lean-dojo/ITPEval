;; Statement-only formalization of thousand-theorems corpus artifact Q257387,
;; "Vitali theorem": a set obtained by choosing one representative from each
;; rational-translation class in the real interval [0,1] is not Borel
;; measurable. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present arbitrary real-field and set codes.  The
;; predicates below explicitly characterize a Dedekind-complete ordered field,
;; its order topology, the Borel sigma algebra, and the fixed representative
;; choice used to define the source Vitali set.

(defstub q257387-r-member-p (real value) t)
(defstub q257387-r-zero (real) t)
(defstub q257387-r-one (real) t)
(defstub q257387-r-add (real left right) t)
(defstub q257387-r-multiply (real left right) t)
(defstub q257387-r-negate (real value) t)
(defstub q257387-r-inverse (real value) t)
(defstub q257387-r-less (real left right) t)

(defstub q257387-set-member-p (set value) t)
(defstub q257387-set-sequence-value (sequence index) t)
(defstub q257387-family-member-p (family set) t)

(defstub q257387-borel-family (real) t)
(defstub q257387-selected-representative (real value) t)
(defstub q257387-vitali-set-code (real) t)

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun q257387-r-leq (real left right)
  (not (q257387-r-less real right left)))

(defun q257387-r-subtract (real left right)
  (q257387-r-add
   real left (q257387-r-negate real right)))

(defun-sk q257387-valid-set-p (real set)
  (forall (x)
    (implies
     (q257387-set-member-p set x)
     (q257387-r-member-p real x))))

(defun-sk q257387-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q257387-r-member-p real x)
      (q257387-r-member-p real y)
      (q257387-r-member-p real z))
     (let* ((zero (q257387-r-zero real))
            (one (q257387-r-one real))
            (xy-add (q257387-r-add real x y))
            (yz-add (q257387-r-add real y z))
            (xy-mul (q257387-r-multiply real x y))
            (yz-mul (q257387-r-multiply real y z))
            (neg-x (q257387-r-negate real x))
            (inv-x (q257387-r-inverse real x)))
       (and
        (q257387-r-member-p real xy-add)
        (q257387-r-member-p real xy-mul)
        (q257387-r-member-p real neg-x)
        (q257387-r-member-p real inv-x)
        (equal
         (q257387-r-add real xy-add z)
         (q257387-r-add real x yz-add))
        (equal xy-add (q257387-r-add real y x))
        (equal (q257387-r-add real x zero) x)
        (equal (q257387-r-add real x neg-x) zero)
        (equal
         (q257387-r-multiply real xy-mul z)
         (q257387-r-multiply real x yz-mul))
        (equal xy-mul (q257387-r-multiply real y x))
        (equal (q257387-r-multiply real x one) x)
        (equal (q257387-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q257387-r-multiply real x inv-x)
          one))
        (equal
         (q257387-r-multiply
          real x (q257387-r-add real y z))
         (q257387-r-add
          real
          (q257387-r-multiply real x y)
          (q257387-r-multiply real x z))))))))

(defun-sk q257387-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q257387-r-member-p real x)
      (q257387-r-member-p real y)
      (q257387-r-member-p real z))
     (let ((zero (q257387-r-zero real)))
       (and
        (not (q257387-r-less real x x))
        (or
         (equal x y)
         (q257387-r-less real x y)
         (q257387-r-less real y x))
        (implies
         (and
          (q257387-r-less real x y)
          (q257387-r-less real y z))
         (q257387-r-less real x z))
        (implies
         (q257387-r-less real x y)
         (q257387-r-less
          real
          (q257387-r-add real x z)
          (q257387-r-add real y z)))
        (implies
         (and
          (q257387-r-less real zero x)
          (q257387-r-less real zero y))
         (q257387-r-less
          real zero
          (q257387-r-multiply real x y))))))))

(defun-sk q257387-set-nonempty-p (real set)
  (exists (x)
    (and
     (q257387-r-member-p real x)
     (q257387-set-member-p set x))))

(defun-sk q257387-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q257387-r-member-p real x)
      (q257387-set-member-p set x))
     (q257387-r-leq real x bound))))

(defun-sk q257387-bounded-above-p (real set)
  (exists (bound)
    (and
     (q257387-r-member-p real bound)
     (q257387-upper-bound-p real set bound))))

(defun-sk q257387-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q257387-r-member-p real supremum)
     (q257387-upper-bound-p real set supremum)
     (implies
      (and
       (q257387-r-member-p real bound)
       (q257387-upper-bound-p real set bound))
      (q257387-r-leq real supremum bound)))))

(defun-sk q257387-supremum-exists-p (real set)
  (exists (supremum)
    (q257387-supremum-p real set supremum)))

(defun-sk q257387-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q257387-valid-set-p real set)
      (q257387-set-nonempty-p real set)
      (q257387-bounded-above-p real set))
     (q257387-supremum-exists-p real set))))

(defun q257387-real-field-p (real)
  (let ((zero (q257387-r-zero real))
        (one (q257387-r-one real)))
    (and
     (q257387-r-member-p real zero)
     (q257387-r-member-p real one)
     (not (equal zero one))
     (q257387-r-field-laws-p real)
     (q257387-r-order-laws-p real)
     (q257387-r-less real zero one)
     (q257387-dedekind-complete-p real))))

;; Exact embedding of ACL2 rationals into the presented real field.

(defun q257387-natural-cast (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q257387-r-zero real)
    (q257387-r-add
     real
     (q257387-r-one real)
     (q257387-natural-cast real (1- n)))))

(defun q257387-integer-cast (real n)
  (if (and (integerp n) (< n 0))
      (q257387-r-negate
       real
       (q257387-natural-cast real (- n)))
    (q257387-natural-cast real (nfix n))))

(defun q257387-rational-cast (real q)
  (if (rationalp q)
      (q257387-r-multiply
       real
       (q257387-integer-cast real (numerator q))
       (q257387-r-inverse
        real
        (q257387-integer-cast real (denominator q))))
    (q257387-r-zero real)))

(defun-sk q257387-rational-cast-injective-p (real)
  (forall (q r)
    (implies
     (and
      (rationalp q)
      (rationalp r)
      (equal
       (q257387-rational-cast real q)
       (q257387-rational-cast real r)))
     (equal q r))))

;; Arbitrary subsets and sigma algebras over the real carrier.

(defun-sk q257387-set-equiv-p (real left right)
  (forall (x)
    (implies
     (q257387-r-member-p real x)
     (iff
      (q257387-set-member-p left x)
      (q257387-set-member-p right x)))))

(defun-sk q257387-empty-set-p (real set)
  (forall (x)
    (iff
     (q257387-set-member-p set x)
     (and (q257387-r-member-p real x) nil))))

(defun-sk q257387-complement-set-p
    (real set complement)
  (forall (x)
    (iff
     (q257387-set-member-p complement x)
     (and
      (q257387-r-member-p real x)
      (not (q257387-set-member-p set x))))))

(defun-sk q257387-set-sequence-p (real sequence)
  (forall (n)
    (implies
     (natp n)
     (q257387-valid-set-p
      real
      (q257387-set-sequence-value sequence n)))))

(defun-sk q257387-sequence-union-member-p
    (sequence x)
  (exists (n)
    (and
     (natp n)
     (q257387-set-member-p
      (q257387-set-sequence-value sequence n)
      x))))

(defun-sk q257387-sequence-union-set-p
    (real sequence union)
  (forall (x)
    (iff
     (q257387-set-member-p union x)
     (and
      (q257387-r-member-p real x)
      (q257387-sequence-union-member-p sequence x)))))

(defun-sk q257387-family-extensional-p
    (real family)
  (forall (left right)
    (implies
     (q257387-set-equiv-p real left right)
     (iff
      (q257387-family-member-p family left)
      (q257387-family-member-p family right)))))

(defun-sk q257387-family-valid-p (real family)
  (forall (set)
    (implies
     (q257387-family-member-p family set)
     (q257387-valid-set-p real set))))

(defun-sk q257387-empty-member-exists-p
    (real family)
  (exists (empty)
    (and
     (q257387-empty-set-p real empty)
     (q257387-family-member-p family empty))))

(defun-sk q257387-complement-member-exists-p
    (real family set)
  (exists (complement)
    (and
     (q257387-complement-set-p real set complement)
     (q257387-family-member-p family complement))))

(defun-sk q257387-family-complements-p
    (real family)
  (forall (set)
    (implies
     (q257387-family-member-p family set)
     (q257387-complement-member-exists-p
      real family set))))

(defun-sk q257387-family-sequence-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q257387-family-member-p
      family
      (q257387-set-sequence-value sequence n)))))

(defun-sk q257387-union-member-exists-p
    (real family sequence)
  (exists (union)
    (and
     (q257387-sequence-union-set-p real sequence union)
     (q257387-family-member-p family union))))

(defun-sk q257387-family-sequence-unions-p
    (real family)
  (forall (sequence)
    (implies
     (and
      (q257387-set-sequence-p real sequence)
      (q257387-family-sequence-p family sequence))
     (q257387-union-member-exists-p
      real family sequence))))

(defun q257387-sigma-algebra-p (real family)
  (and
   (q257387-family-extensional-p real family)
   (q257387-family-valid-p real family)
   (q257387-empty-member-exists-p real family)
   (q257387-family-complements-p real family)
   (q257387-family-sequence-unions-p real family)))

;; The order topology and its generated Borel sigma algebra.

(defun-sk q257387-open-neighborhood-p
    (real set point lower upper)
  (forall (x)
    (implies
     (and
      (q257387-r-member-p real x)
      (q257387-r-less real lower x)
      (q257387-r-less real x upper))
     (q257387-set-member-p set x))))

(defun-sk q257387-open-neighborhood-exists-p
    (real set point)
  (exists (lower upper)
    (and
     (q257387-r-member-p real lower)
     (q257387-r-member-p real upper)
     (q257387-r-less real lower point)
     (q257387-r-less real point upper)
     (q257387-open-neighborhood-p
      real set point lower upper))))

(defun-sk q257387-open-set-p (real set)
  (forall (point)
    (and
     (q257387-valid-set-p real set)
     (implies
      (and
       (q257387-r-member-p real point)
       (q257387-set-member-p set point))
      (q257387-open-neighborhood-exists-p
       real set point)))))

(defun-sk q257387-family-contains-open-sets-p
    (real family)
  (forall (set)
    (implies
     (q257387-open-set-p real set)
     (q257387-family-member-p family set))))

(defun-sk q257387-borel-minimal-p
    (real borel)
  (forall (family set)
    (implies
     (and
      (q257387-sigma-algebra-p real family)
      (q257387-family-contains-open-sets-p real family)
      (q257387-family-member-p borel set))
     (q257387-family-member-p family set))))

(defun q257387-borel-space-p (real)
  (let ((borel (q257387-borel-family real)))
    (and
     (q257387-sigma-algebra-p real borel)
     (q257387-family-contains-open-sets-p real borel)
     (q257387-borel-minimal-p real borel))))

;; The source setoid relation: x and y differ by a rational real number.

(defun-sk q257387-rationally-related-p
    (real x y)
  (exists (q)
    (and
     (rationalp q)
     (equal
      (q257387-r-subtract real x y)
      (q257387-rational-cast real q)))))

(defun q257387-unit-interval-member-p (real x)
  (and
   (q257387-r-member-p real x)
   (q257387-r-leq real (q257387-r-zero real) x)
   (q257387-r-leq real x (q257387-r-one real))))

;; SELECTED-REPRESENTATIVE is the fixed Classical.choose representative from
;; each quotient class.  The first law puts it in the same class and in
;; [0,1]; the second says that it depends only on the quotient class.

(defun-sk q257387-representative-value-laws-p (real)
  (forall (x)
    (implies
     (q257387-unit-interval-member-p real x)
     (let ((representative
            (q257387-selected-representative real x)))
       (and
        (q257387-unit-interval-member-p real representative)
        (q257387-rationally-related-p
         real x representative))))))

(defun-sk q257387-representative-class-laws-p (real)
  (forall (x y)
    (implies
     (and
      (q257387-unit-interval-member-p real x)
      (q257387-unit-interval-member-p real y)
      (q257387-rationally-related-p real x y))
     (equal
      (q257387-selected-representative real x)
      (q257387-selected-representative real y)))))

(defun q257387-representative-choice-p (real)
  (and
   (q257387-representative-value-laws-p real)
   (q257387-representative-class-laws-p real)))

(defun-sk q257387-representative-preimage-exists-p
    (real representative)
  (exists (x)
    (and
     (q257387-unit-interval-member-p real x)
     (equal
      (q257387-selected-representative real x)
      representative))))

(defun-sk q257387-vitali-set-p (real)
  (forall (representative)
    (iff
     (q257387-set-member-p
      (q257387-vitali-set-code real)
      representative)
     (and
      (q257387-r-member-p real representative)
      (q257387-representative-preimage-exists-p
       real representative)))))

(defun-sk thousand-theorems-q257387-vitali-theorem-statement ()
  (forall (real)
    (implies
     (and
      (q257387-real-field-p real)
      (q257387-rational-cast-injective-p real)
      (q257387-borel-space-p real)
      (q257387-representative-choice-p real)
      (q257387-valid-set-p
       real (q257387-vitali-set-code real))
      (q257387-vitali-set-p real))
     (not
      (q257387-family-member-p
       (q257387-borel-family real)
       (q257387-vitali-set-code real))))))

(value-triple :itpeval-statement-checked)
:q
