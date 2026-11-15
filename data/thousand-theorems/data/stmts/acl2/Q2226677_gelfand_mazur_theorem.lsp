;; Statement-only formalization of thousand-theorems corpus artifact Q2226677,
;; "Gelfand–Mazur theorem": a complete complex normed ring whose nonzero
;; elements are exactly its units is algebra-equivalent to the complex
;; numbers through the natural scalar map. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present arbitrary real, complex, and algebra
;; carriers. A Dedekind-complete ordered field presents the real numbers;
;; real/imaginary coordinates and the Euclidean norm present the complex
;; numbers. All ring, normed-algebra, completeness, unit, and typing laws
;; used by the source declaration are explicit in the statement predicate.

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defstub q2226677-r-member-p (real value) t)
(defstub q2226677-r-zero (real) t)
(defstub q2226677-r-one (real) t)
(defstub q2226677-r-add (real left right) t)
(defstub q2226677-r-multiply (real left right) t)
(defstub q2226677-r-negate (real value) t)
(defstub q2226677-r-inverse (real value) t)
(defstub q2226677-r-less (real left right) t)
(defstub q2226677-r-set-member-p (real set value) t)

(defun q2226677-r-leq (real left right)
  (not (q2226677-r-less real right left)))

(defun-sk q2226677-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2226677-r-member-p real x)
      (q2226677-r-member-p real y)
      (q2226677-r-member-p real z))
     (let* ((zero (q2226677-r-zero real))
            (one (q2226677-r-one real))
            (xy-add (q2226677-r-add real x y))
            (yz-add (q2226677-r-add real y z))
            (xy-mul (q2226677-r-multiply real x y))
            (yz-mul (q2226677-r-multiply real y z))
            (neg-x (q2226677-r-negate real x))
            (inv-x (q2226677-r-inverse real x)))
       (and
        (q2226677-r-member-p real xy-add)
        (q2226677-r-member-p real xy-mul)
        (q2226677-r-member-p real neg-x)
        (q2226677-r-member-p real inv-x)
        (equal
         (q2226677-r-add real xy-add z)
         (q2226677-r-add real x yz-add))
        (equal xy-add (q2226677-r-add real y x))
        (equal (q2226677-r-add real x zero) x)
        (equal (q2226677-r-add real x neg-x) zero)
        (equal
         (q2226677-r-multiply real xy-mul z)
         (q2226677-r-multiply real x yz-mul))
        (equal xy-mul (q2226677-r-multiply real y x))
        (equal (q2226677-r-multiply real x one) x)
        (equal (q2226677-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2226677-r-multiply real x inv-x)
          one))
        (equal
         (q2226677-r-multiply
          real x (q2226677-r-add real y z))
         (q2226677-r-add
          real
          (q2226677-r-multiply real x y)
          (q2226677-r-multiply real x z))))))))

(defun-sk q2226677-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2226677-r-member-p real x)
      (q2226677-r-member-p real y)
      (q2226677-r-member-p real z))
     (let ((zero (q2226677-r-zero real)))
       (and
        (not (q2226677-r-less real x x))
        (or
         (equal x y)
         (q2226677-r-less real x y)
         (q2226677-r-less real y x))
        (implies
         (and
          (q2226677-r-less real x y)
          (q2226677-r-less real y z))
         (q2226677-r-less real x z))
        (implies
         (q2226677-r-less real x y)
         (q2226677-r-less
          real
          (q2226677-r-add real x z)
          (q2226677-r-add real y z)))
        (implies
         (and
          (q2226677-r-less real zero x)
          (q2226677-r-less real zero y))
         (q2226677-r-less
          real zero
          (q2226677-r-multiply real x y))))))))

(defun-sk q2226677-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2226677-r-member-p real x)
     (q2226677-r-set-member-p real set x))))

(defun-sk q2226677-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2226677-r-member-p real x)
      (q2226677-r-set-member-p real set x))
     (q2226677-r-leq real x bound))))

(defun-sk q2226677-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2226677-r-member-p real bound)
     (q2226677-r-upper-bound-p real set bound))))

(defun-sk q2226677-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2226677-r-member-p real supremum)
     (q2226677-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2226677-r-member-p real bound)
       (q2226677-r-upper-bound-p real set bound))
      (q2226677-r-leq real supremum bound)))))

(defun-sk q2226677-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2226677-r-supremum-p real set supremum)))

(defun-sk q2226677-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2226677-r-set-nonempty-p real set)
      (q2226677-r-bounded-above-p real set))
     (q2226677-r-supremum-exists-p real set))))

(defun q2226677-real-field-p (real)
  (let ((zero (q2226677-r-zero real))
        (one (q2226677-r-one real)))
    (and
     (q2226677-r-member-p real zero)
     (q2226677-r-member-p real one)
     (not (equal zero one))
     (q2226677-r-field-laws-p real)
     (q2226677-r-order-laws-p real)
     (q2226677-r-less real zero one)
     (q2226677-r-dedekind-complete-p real))))

;; The complex numbers as the Euclidean real-coordinate field.

(defstub q2226677-c-member-p (complex value) t)
(defstub q2226677-c-zero (complex) t)
(defstub q2226677-c-one (complex) t)
(defstub q2226677-c-add (complex left right) t)
(defstub q2226677-c-multiply (complex left right) t)
(defstub q2226677-c-negate (complex value) t)
(defstub q2226677-c-inverse (complex value) t)
(defstub q2226677-c-norm (real complex value) t)
(defstub q2226677-c-of-real (real complex value) t)
(defstub q2226677-c-re (real complex value) t)
(defstub q2226677-c-im (real complex value) t)
(defstub q2226677-c-I (complex) t)

(defun-sk q2226677-c-field-laws-p (complex)
  (forall (x y z)
    (implies
     (and
      (q2226677-c-member-p complex x)
      (q2226677-c-member-p complex y)
      (q2226677-c-member-p complex z))
     (let* ((zero (q2226677-c-zero complex))
            (one (q2226677-c-one complex))
            (xy-add (q2226677-c-add complex x y))
            (yz-add (q2226677-c-add complex y z))
            (xy-mul (q2226677-c-multiply complex x y))
            (yz-mul (q2226677-c-multiply complex y z))
            (neg-x (q2226677-c-negate complex x))
            (inv-x (q2226677-c-inverse complex x)))
       (and
        (q2226677-c-member-p complex xy-add)
        (q2226677-c-member-p complex xy-mul)
        (q2226677-c-member-p complex neg-x)
        (q2226677-c-member-p complex inv-x)
        (equal
         (q2226677-c-add complex xy-add z)
         (q2226677-c-add complex x yz-add))
        (equal xy-add (q2226677-c-add complex y x))
        (equal (q2226677-c-add complex x zero) x)
        (equal (q2226677-c-add complex x neg-x) zero)
        (equal
         (q2226677-c-multiply complex xy-mul z)
         (q2226677-c-multiply complex x yz-mul))
        (equal xy-mul (q2226677-c-multiply complex y x))
        (equal (q2226677-c-multiply complex x one) x)
        (equal (q2226677-c-inverse complex zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2226677-c-multiply complex x inv-x)
          one))
        (equal
         (q2226677-c-multiply
          complex x (q2226677-c-add complex y z))
         (q2226677-c-add
          complex
          (q2226677-c-multiply complex x y)
          (q2226677-c-multiply complex x z))))))))

(defun-sk q2226677-c-norm-laws-p (real complex)
  (forall (x y)
    (implies
     (and
      (q2226677-c-member-p complex x)
      (q2226677-c-member-p complex y))
     (let ((zero-c (q2226677-c-zero complex))
           (zero-r (q2226677-r-zero real))
           (norm-x (q2226677-c-norm real complex x))
           (norm-y (q2226677-c-norm real complex y)))
       (and
        (q2226677-r-member-p real norm-x)
        (q2226677-r-member-p real norm-y)
        (q2226677-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-c))
        (equal
         (q2226677-c-norm
          real complex (q2226677-c-negate complex x))
         norm-x)
        (q2226677-r-leq
         real
         (q2226677-c-norm
          real complex (q2226677-c-add complex x y))
         (q2226677-r-add real norm-x norm-y))
        (equal
         (q2226677-c-norm
          real complex (q2226677-c-multiply complex x y))
         (q2226677-r-multiply real norm-x norm-y)))))))

(defun-sk q2226677-c-coordinate-laws-p (real complex)
  (forall (a b z)
    (implies
     (and
      (q2226677-r-member-p real a)
      (q2226677-r-member-p real b)
      (q2226677-c-member-p complex z))
     (let* ((zero-r (q2226677-r-zero real))
            (one-r (q2226677-r-one real))
            (zero-c (q2226677-c-zero complex))
            (one-c (q2226677-c-one complex))
            (imaginary-unit (q2226677-c-I complex))
            (of-a (q2226677-c-of-real real complex a))
            (of-b (q2226677-c-of-real real complex b))
            (re-z (q2226677-c-re real complex z))
            (im-z (q2226677-c-im real complex z))
            (norm-z (q2226677-c-norm real complex z)))
       (and
        (q2226677-c-member-p complex imaginary-unit)
        (q2226677-c-member-p complex of-a)
        (q2226677-r-member-p real re-z)
        (q2226677-r-member-p real im-z)
        (equal
         (q2226677-c-of-real real complex zero-r)
         zero-c)
        (equal
         (q2226677-c-of-real real complex one-r)
         one-c)
        (equal
         (q2226677-c-of-real
          real complex (q2226677-r-add real a b))
         (q2226677-c-add complex of-a of-b))
        (equal
         (q2226677-c-of-real
          real complex (q2226677-r-multiply real a b))
         (q2226677-c-multiply complex of-a of-b))
        (equal
         (q2226677-c-of-real
          real complex (q2226677-r-negate real a))
         (q2226677-c-negate complex of-a))
        (equal (q2226677-c-re real complex of-a) a)
        (equal
         (q2226677-c-im real complex of-a)
         zero-r)
        (equal
         (q2226677-c-re real complex imaginary-unit)
         zero-r)
        (equal
         (q2226677-c-im real complex imaginary-unit)
         one-r)
        (equal
         (q2226677-c-multiply
          complex imaginary-unit imaginary-unit)
         (q2226677-c-negate complex one-c))
        (equal
         z
         (q2226677-c-add
          complex
          (q2226677-c-of-real real complex re-z)
          (q2226677-c-multiply
           complex
           (q2226677-c-of-real real complex im-z)
           imaginary-unit)))
        (equal
         (q2226677-r-multiply real norm-z norm-z)
         (q2226677-r-add
          real
          (q2226677-r-multiply real re-z re-z)
          (q2226677-r-multiply real im-z im-z))))))))

(defun q2226677-complex-field-p (real complex)
  (let ((zero (q2226677-c-zero complex))
        (one (q2226677-c-one complex)))
    (and
     (q2226677-real-field-p real)
     (q2226677-c-member-p complex zero)
     (q2226677-c-member-p complex one)
     (not (equal zero one))
     (q2226677-c-field-laws-p complex)
     (q2226677-c-norm-laws-p real complex)
     (q2226677-c-coordinate-laws-p real complex))))

;; An arbitrary complete normed ring and its natural complex algebra map.

(defstub q2226677-a-member-p (algebra value) t)
(defstub q2226677-a-zero (algebra) t)
(defstub q2226677-a-one (algebra) t)
(defstub q2226677-a-add (algebra left right) t)
(defstub q2226677-a-multiply (algebra left right) t)
(defstub q2226677-a-negate (algebra value) t)
(defstub q2226677-a-norm (real algebra value) t)
(defstub q2226677-algebra-map
  (complex algebra scalar)
  t)
(defstub q2226677-a-sequence-value
  (algebra sequence index)
  t)

(defun q2226677-a-subtract (algebra left right)
  (q2226677-a-add
   algebra left (q2226677-a-negate algebra right)))

(defun-sk q2226677-a-ring-laws-p (algebra)
  (forall (x y z)
    (implies
     (and
      (q2226677-a-member-p algebra x)
      (q2226677-a-member-p algebra y)
      (q2226677-a-member-p algebra z))
     (let* ((zero (q2226677-a-zero algebra))
            (one (q2226677-a-one algebra))
            (xy-add (q2226677-a-add algebra x y))
            (yz-add (q2226677-a-add algebra y z))
            (xy-mul (q2226677-a-multiply algebra x y))
            (yz-mul (q2226677-a-multiply algebra y z))
            (neg-x (q2226677-a-negate algebra x)))
       (and
        (q2226677-a-member-p algebra xy-add)
        (q2226677-a-member-p algebra xy-mul)
        (q2226677-a-member-p algebra neg-x)
        (equal
         (q2226677-a-add algebra xy-add z)
         (q2226677-a-add algebra x yz-add))
        (equal xy-add (q2226677-a-add algebra y x))
        (equal (q2226677-a-add algebra x zero) x)
        (equal (q2226677-a-add algebra x neg-x) zero)
        (equal
         (q2226677-a-multiply algebra xy-mul z)
         (q2226677-a-multiply algebra x yz-mul))
        (equal (q2226677-a-multiply algebra x one) x)
        (equal (q2226677-a-multiply algebra one x) x)
        (equal
         (q2226677-a-multiply
          algebra x (q2226677-a-add algebra y z))
         (q2226677-a-add
          algebra
          (q2226677-a-multiply algebra x y)
          (q2226677-a-multiply algebra x z)))
        (equal
         (q2226677-a-multiply
          algebra (q2226677-a-add algebra x y) z)
         (q2226677-a-add
          algebra
          (q2226677-a-multiply algebra x z)
          (q2226677-a-multiply algebra y z))))))))

(defun-sk q2226677-a-norm-laws-p (real algebra)
  (forall (x y)
    (implies
     (and
      (q2226677-a-member-p algebra x)
      (q2226677-a-member-p algebra y))
     (let ((zero-r (q2226677-r-zero real))
           (one-r (q2226677-r-one real))
           (zero-a (q2226677-a-zero algebra))
           (one-a (q2226677-a-one algebra))
           (norm-x (q2226677-a-norm real algebra x))
           (norm-y (q2226677-a-norm real algebra y)))
       (and
        (q2226677-r-member-p real norm-x)
        (q2226677-r-member-p real norm-y)
        (q2226677-r-leq real zero-r norm-x)
        (iff (equal norm-x zero-r)
             (equal x zero-a))
        (equal
         (q2226677-a-norm
          real algebra (q2226677-a-negate algebra x))
         norm-x)
        (q2226677-r-leq
         real
         (q2226677-a-norm
          real algebra (q2226677-a-add algebra x y))
         (q2226677-r-add real norm-x norm-y))
        (q2226677-r-leq
         real
         (q2226677-a-norm
          real algebra (q2226677-a-multiply algebra x y))
         (q2226677-r-multiply real norm-x norm-y))
        (equal
         (q2226677-a-norm real algebra zero-a)
         zero-r)
        (equal
         (q2226677-a-norm real algebra one-a)
         one-r))))))

(defun-sk q2226677-algebra-laws-p
    (real complex algebra)
  (forall (c d x)
    (implies
     (and
      (q2226677-c-member-p complex c)
      (q2226677-c-member-p complex d)
      (q2226677-a-member-p algebra x))
     (let ((map-c
            (q2226677-algebra-map complex algebra c)))
       (and
        (q2226677-a-member-p algebra map-c)
        (equal
         (q2226677-algebra-map
          complex algebra (q2226677-c-zero complex))
         (q2226677-a-zero algebra))
        (equal
         (q2226677-algebra-map
          complex algebra (q2226677-c-one complex))
         (q2226677-a-one algebra))
        (equal
         (q2226677-algebra-map
          complex algebra (q2226677-c-add complex c d))
         (q2226677-a-add
          algebra
          map-c
          (q2226677-algebra-map complex algebra d)))
        (equal
         (q2226677-algebra-map
          complex algebra
          (q2226677-c-multiply complex c d))
         (q2226677-a-multiply
          algebra
          map-c
          (q2226677-algebra-map complex algebra d)))
        (equal
         (q2226677-algebra-map
          complex algebra (q2226677-c-negate complex c))
         (q2226677-a-negate algebra map-c))
        (equal
         (q2226677-a-multiply algebra map-c x)
         (q2226677-a-multiply algebra x map-c))
        (q2226677-r-leq
         real
         (q2226677-a-norm
          real algebra
          (q2226677-a-multiply algebra map-c x))
         (q2226677-r-multiply
          real
          (q2226677-c-norm real complex c)
          (q2226677-a-norm real algebra x))))))))

(defun q2226677-a-distance (real algebra x y)
  (q2226677-a-norm
   real algebra (q2226677-a-subtract algebra x y)))

(defun-sk q2226677-a-sequence-typed-p
    (algebra sequence)
  (forall (n)
    (implies
     (natp n)
     (q2226677-a-member-p
      algebra
      (q2226677-a-sequence-value algebra sequence n)))))

(defun-sk q2226677-a-cauchy-tail-p
    (real algebra sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q2226677-r-less
      real
      (q2226677-a-distance
       real algebra
       (q2226677-a-sequence-value algebra sequence m)
       (q2226677-a-sequence-value algebra sequence n))
      epsilon))))

(defun-sk q2226677-a-cauchy-cutoff-exists-p
    (real algebra sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q2226677-a-cauchy-tail-p
      real algebra sequence epsilon cutoff))))

(defun-sk q2226677-a-cauchy-p
    (real algebra sequence)
  (forall (epsilon)
    (implies
     (and
      (q2226677-r-member-p real epsilon)
      (q2226677-r-less
       real (q2226677-r-zero real) epsilon))
     (q2226677-a-cauchy-cutoff-exists-p
      real algebra sequence epsilon))))

(defun-sk q2226677-a-convergence-tail-p
    (real algebra sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q2226677-r-less
      real
      (q2226677-a-distance
       real algebra
       (q2226677-a-sequence-value algebra sequence n)
       limit)
      epsilon))))

(defun-sk q2226677-a-convergence-cutoff-exists-p
    (real algebra sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q2226677-a-convergence-tail-p
      real algebra sequence limit epsilon cutoff))))

(defun-sk q2226677-a-converges-p
    (real algebra sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q2226677-r-member-p real epsilon)
      (q2226677-r-less
       real (q2226677-r-zero real) epsilon))
     (q2226677-a-convergence-cutoff-exists-p
      real algebra sequence limit epsilon))))

(defun-sk q2226677-a-limit-exists-p
    (real algebra sequence)
  (exists (limit)
    (and
     (q2226677-a-member-p algebra limit)
     (q2226677-a-converges-p
      real algebra sequence limit))))

(defun-sk q2226677-a-complete-space-p
    (real algebra)
  (forall (sequence)
    (implies
     (and
      (q2226677-a-sequence-typed-p algebra sequence)
      (q2226677-a-cauchy-p real algebra sequence))
     (q2226677-a-limit-exists-p
      real algebra sequence))))

(defun q2226677-complete-complex-normed-ring-p
    (real complex algebra)
  (and
   (q2226677-a-member-p
    algebra (q2226677-a-zero algebra))
   (q2226677-a-member-p
    algebra (q2226677-a-one algebra))
   (q2226677-a-ring-laws-p algebra)
   (q2226677-a-norm-laws-p real algebra)
   (q2226677-algebra-laws-p real complex algebra)
   (q2226677-a-complete-space-p real algebra)))

;; ISUNIT(a) is represented by a two-sided inverse inside the algebra carrier.

(defun-sk q2226677-a-unit-p (algebra element)
  (exists (inverse)
    (and
     (q2226677-a-member-p algebra inverse)
     (equal
      (q2226677-a-multiply algebra element inverse)
      (q2226677-a-one algebra))
     (equal
      (q2226677-a-multiply algebra inverse element)
      (q2226677-a-one algebra)))))

(defun-sk q2226677-nonzero-iff-unit-p (algebra)
  (forall (element)
    (implies
     (q2226677-a-member-p algebra element)
     (iff
      (q2226677-a-unit-p algebra element)
      (not
       (equal element (q2226677-a-zero algebra)))))))

;; Under the algebra laws, injectivity and surjectivity of the natural
;; algebra map are exactly the existence of an algebra equivalence whose
;; forward function is that map.

(defun-sk q2226677-algebra-map-injective-p
    (complex algebra)
  (forall (left right)
    (implies
     (and
      (q2226677-c-member-p complex left)
      (q2226677-c-member-p complex right)
      (equal
       (q2226677-algebra-map complex algebra left)
       (q2226677-algebra-map complex algebra right)))
     (equal left right))))

(defun-sk q2226677-algebra-map-preimage-exists-p
    (complex algebra element)
  (exists (scalar)
    (and
     (q2226677-c-member-p complex scalar)
     (equal
      (q2226677-algebra-map complex algebra scalar)
      element))))

(defun-sk q2226677-algebra-map-surjective-p
    (complex algebra)
  (forall (element)
    (implies
     (q2226677-a-member-p algebra element)
     (q2226677-algebra-map-preimage-exists-p
      complex algebra element))))

(defun q2226677-natural-algebra-equivalence-p
    (complex algebra)
  (and
   (q2226677-algebra-map-injective-p complex algebra)
   (q2226677-algebra-map-surjective-p complex algebra)))

(defun thousand-theorems-q2226677-gelfand-mazur-theorem-statement
    (real complex algebra)
  (implies
   (and
    (q2226677-complex-field-p real complex)
    (q2226677-complete-complex-normed-ring-p
     real complex algebra)
    (q2226677-nonzero-iff-unit-p algebra))
   (q2226677-natural-algebra-equivalence-p
    complex algebra)))

(value-triple :itpeval-statement-checked)
:q
