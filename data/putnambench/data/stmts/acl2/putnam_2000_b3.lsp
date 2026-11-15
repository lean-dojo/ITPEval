;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_b3:
;; zero counts with multiplicity for successive derivatives of a finite real
;; sine sum are nondecreasing and converge to twice the highest nonzero
;; frequency. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present an arbitrary ordered field. The final
;; predicate explicitly requires the Archimedean real-closed-field laws.
;; Every finite tuple of source coefficients and every algebraic unit-circle
;; root lies in such a real-closed subfield of the reals, while every such
;; field embeds order-preservingly in the reals.

(defstub putnam-2000-b3-real-p (x) t)
(defstub putnam-2000-b3-add-op (x y) t)
(defstub putnam-2000-b3-mul-op (x y) t)
(defstub putnam-2000-b3-neg-op (x) t)
(defstub putnam-2000-b3-inv-op (x) t)
(defstub putnam-2000-b3-less-op (x y) t)

(defun putnam-2000-b3-member-p (x)
  (if (putnam-2000-b3-real-p x) t nil))

(defun putnam-2000-b3-add (x y)
  (putnam-2000-b3-add-op x y))

(defun putnam-2000-b3-mul (x y)
  (putnam-2000-b3-mul-op x y))

(defun putnam-2000-b3-neg (x)
  (putnam-2000-b3-neg-op x))

(defun putnam-2000-b3-inv (x)
  (putnam-2000-b3-inv-op x))

(defun putnam-2000-b3-less (x y)
  (if (putnam-2000-b3-less-op x y) t nil))

(defun-sk putnam-2000-b3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-2000-b3-member-p x)
      (putnam-2000-b3-member-p y)
      (putnam-2000-b3-member-p z))
     (and
      (putnam-2000-b3-member-p
       (putnam-2000-b3-add x y))
      (putnam-2000-b3-member-p
       (putnam-2000-b3-mul x y))
      (putnam-2000-b3-member-p
       (putnam-2000-b3-neg x))
      (putnam-2000-b3-member-p
       (putnam-2000-b3-inv x))
      (equal
       (putnam-2000-b3-add
        (putnam-2000-b3-add x y) z)
       (putnam-2000-b3-add
        x (putnam-2000-b3-add y z)))
      (equal
       (putnam-2000-b3-add x y)
       (putnam-2000-b3-add y x))
      (equal (putnam-2000-b3-add x zero) x)
      (equal
       (putnam-2000-b3-add x (putnam-2000-b3-neg x))
       zero)
      (equal
       (putnam-2000-b3-mul
        (putnam-2000-b3-mul x y) z)
       (putnam-2000-b3-mul
        x (putnam-2000-b3-mul y z)))
      (equal
       (putnam-2000-b3-mul x y)
       (putnam-2000-b3-mul y x))
      (equal (putnam-2000-b3-mul x one) x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-2000-b3-mul
         x (putnam-2000-b3-inv x))
        one))
      (equal
       (putnam-2000-b3-mul
        x (putnam-2000-b3-add y z))
       (putnam-2000-b3-add
        (putnam-2000-b3-mul x y)
        (putnam-2000-b3-mul x z)))))))

(defun-sk putnam-2000-b3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (putnam-2000-b3-member-p x)
      (putnam-2000-b3-member-p y)
      (putnam-2000-b3-member-p z))
     (and
      (not (putnam-2000-b3-less x x))
      (or
       (equal x y)
       (putnam-2000-b3-less x y)
       (putnam-2000-b3-less y x))
      (implies
       (and
        (putnam-2000-b3-less x y)
        (putnam-2000-b3-less y z))
       (putnam-2000-b3-less x z))
      (implies
       (putnam-2000-b3-less x y)
       (putnam-2000-b3-less
        (putnam-2000-b3-add x z)
        (putnam-2000-b3-add y z)))
      (implies
       (and
        (putnam-2000-b3-less zero x)
        (putnam-2000-b3-less zero y))
       (putnam-2000-b3-less
        zero
        (putnam-2000-b3-mul x y)))))))

(defun putnam-2000-b3-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-2000-b3-member-p (car coefficients))
       (putnam-2000-b3-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2000-b3-polynomial-evaluate
    (coefficients x zero)
  (if (consp coefficients)
      (putnam-2000-b3-add
       (car coefficients)
       (putnam-2000-b3-mul
        x
        (putnam-2000-b3-polynomial-evaluate
         (cdr coefficients) x zero)))
    zero))

(defun putnam-2000-b3-odd-degree-polynomial-p
    (coefficients zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2000-b3-coefficient-list-p coefficients)
   (not (equal (car (last coefficients)) zero))
   (evenp (len coefficients))))

(defun-sk putnam-2000-b3-square-root-exists-p (x)
  (exists (root)
    (and
     (putnam-2000-b3-member-p root)
     (equal (putnam-2000-b3-mul root root) x))))

(defun-sk putnam-2000-b3-nonnegative-square-roots-p (zero)
  (forall (x)
    (implies
     (and
      (putnam-2000-b3-member-p x)
      (not (putnam-2000-b3-less x zero)))
     (putnam-2000-b3-square-root-exists-p x))))

(defun-sk putnam-2000-b3-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (putnam-2000-b3-member-p root)
     (equal
      (putnam-2000-b3-polynomial-evaluate
       coefficients root zero)
      zero))))

(defun-sk putnam-2000-b3-odd-polynomial-roots-p (zero)
  (forall (coefficients)
    (implies
     (putnam-2000-b3-odd-degree-polynomial-p
      coefficients zero)
     (putnam-2000-b3-polynomial-root-exists-p
      coefficients zero))))

(defun putnam-2000-b3-embed-natural (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2000-b3-add
     one
     (putnam-2000-b3-embed-natural
      (- n 1) zero one))))

(defun-sk putnam-2000-b3-natural-bound-exists-p
    (x zero one)
  (exists (n)
    (and
     (natp n)
     (putnam-2000-b3-less
      x
      (putnam-2000-b3-embed-natural
       n zero one)))))

(defun-sk putnam-2000-b3-archimedean-p (zero one)
  (forall (x)
    (implies
     (putnam-2000-b3-member-p x)
     (putnam-2000-b3-natural-bound-exists-p
      x zero one))))

(defun putnam-2000-b3-real-field-p (zero one)
  (and
   (putnam-2000-b3-member-p zero)
   (putnam-2000-b3-member-p one)
   (not (equal zero one))
   (putnam-2000-b3-less zero one)
   (putnam-2000-b3-field-laws-p zero one)
   (putnam-2000-b3-order-laws-p zero)
   (putnam-2000-b3-nonnegative-square-roots-p zero)
   (putnam-2000-b3-odd-polynomial-roots-p zero)
   (putnam-2000-b3-archimedean-p zero one)))

(defun putnam-2000-b3-power (base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2000-b3-mul
     base
     (putnam-2000-b3-power
      base (- exponent 1) one))))

;; If (x,y)=(cos theta,sin theta), this recurrence returns
;; (cos(j*theta),sin(j*theta)).

(defun putnam-2000-b3-harmonic-pair
    (j x y zero one)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      (cons one zero)
    (let* ((previous
            (putnam-2000-b3-harmonic-pair
             (- j 1) x y zero one))
           (cosine (car previous))
           (sine (cdr previous)))
      (cons
       (putnam-2000-b3-add
        (putnam-2000-b3-mul cosine x)
        (putnam-2000-b3-neg
         (putnam-2000-b3-mul sine y)))
       (putnam-2000-b3-add
        (putnam-2000-b3-mul cosine y)
        (putnam-2000-b3-mul sine x))))))

(defun putnam-2000-b3-phase-value
    (derivative-order harmonic-pair)
  (case (mod derivative-order 4)
    (0 (cdr harmonic-pair))
    (1 (car harmonic-pair))
    (2 (putnam-2000-b3-neg (cdr harmonic-pair)))
    (otherwise
     (putnam-2000-b3-neg (car harmonic-pair)))))

;; This is the kth derivative divided by the nonzero common factor
;; (2*pi)^k. Removing that factor preserves every zero and multiplicity.

(defun putnam-2000-b3-derivative-value-aux
    (coefficients harmonic derivative-order x y
                  zero one)
  (if (consp coefficients)
      (let* ((pair
              (putnam-2000-b3-harmonic-pair
               harmonic x y zero one))
             (harmonic-value
              (putnam-2000-b3-embed-natural
               harmonic zero one))
             (scale
              (putnam-2000-b3-power
               harmonic-value derivative-order one))
             (term
              (putnam-2000-b3-mul
               (car coefficients)
               (putnam-2000-b3-mul
                scale
                (putnam-2000-b3-phase-value
                 derivative-order pair)))))
        (putnam-2000-b3-add
         term
         (putnam-2000-b3-derivative-value-aux
          (cdr coefficients)
          (+ harmonic 1)
          derivative-order x y zero one)))
    zero))

(defun putnam-2000-b3-derivative-value
    (coefficients derivative-order x y zero one)
  (putnam-2000-b3-derivative-value-aux
   coefficients 1 derivative-order x y zero one))

(defun putnam-2000-b3-unit-circle-p (x y one)
  (and
   (putnam-2000-b3-member-p x)
   (putnam-2000-b3-member-p y)
   (equal
    (putnam-2000-b3-add
     (putnam-2000-b3-mul x x)
     (putnam-2000-b3-mul y y))
    one)))

(defun putnam-2000-b3-lower-derivatives-zero-p
    (coefficients derivative-order multiplicity
                  x y zero one)
  (declare (xargs :measure (nfix multiplicity)))
  (if (zp multiplicity)
      t
    (and
     (equal
      (putnam-2000-b3-derivative-value
       coefficients derivative-order x y zero one)
      zero)
     (putnam-2000-b3-lower-derivatives-zero-p
      coefficients
      (+ derivative-order 1)
      (- multiplicity 1)
      x y zero one))))

(defun putnam-2000-b3-multiplicity-p
    (coefficients derivative-order x y multiplicity
                  zero one)
  (and
   (posp multiplicity)
   (putnam-2000-b3-lower-derivatives-zero-p
    coefficients derivative-order multiplicity
    x y zero one)
   (not
    (equal
     (putnam-2000-b3-derivative-value
      coefficients
      (+ derivative-order multiplicity)
      x y zero one)
     zero))))

;; A root entry is the list (x y multiplicity).

(defun putnam-2000-b3-root-entry-p
    (entry coefficients derivative-order zero one)
  (and
   (true-listp entry)
   (equal (len entry) 3)
   (putnam-2000-b3-unit-circle-p
    (nth 0 entry) (nth 1 entry) one)
   (putnam-2000-b3-multiplicity-p
    coefficients derivative-order
    (nth 0 entry) (nth 1 entry) (nth 2 entry)
    zero one)))

(defun putnam-2000-b3-point-not-in-entries-p
    (x y entries)
  (if (consp entries)
      (and
       (not
        (and
         (equal x (nth 0 (car entries)))
         (equal y (nth 1 (car entries)))))
       (putnam-2000-b3-point-not-in-entries-p
        x y (cdr entries)))
    (equal entries nil)))

(defun putnam-2000-b3-root-entries-p
    (entries coefficients derivative-order zero one)
  (if (consp entries)
      (and
       (putnam-2000-b3-root-entry-p
        (car entries) coefficients derivative-order
        zero one)
       (putnam-2000-b3-point-not-in-entries-p
        (nth 0 (car entries))
        (nth 1 (car entries))
        (cdr entries))
       (putnam-2000-b3-root-entries-p
        (cdr entries) coefficients derivative-order
        zero one))
    (equal entries nil)))

(defun putnam-2000-b3-point-in-entries-p (x y entries)
  (if (consp entries)
      (or
       (and
        (equal x (nth 0 (car entries)))
        (equal y (nth 1 (car entries))))
       (putnam-2000-b3-point-in-entries-p
        x y (cdr entries)))
    nil))

(defun-sk putnam-2000-b3-all-roots-listed-p
    (entries coefficients derivative-order zero one)
  (forall (x y)
    (implies
     (and
      (putnam-2000-b3-unit-circle-p x y one)
      (equal
       (putnam-2000-b3-derivative-value
        coefficients derivative-order x y zero one)
       zero))
     (putnam-2000-b3-point-in-entries-p
      x y entries))))

(defun putnam-2000-b3-exact-root-list-p
    (entries coefficients derivative-order zero one)
  (and
   (true-listp entries)
   (putnam-2000-b3-root-entries-p
    entries coefficients derivative-order zero one)
   (putnam-2000-b3-all-roots-listed-p
    entries coefficients derivative-order zero one)))

(defun putnam-2000-b3-total-multiplicity (entries)
  (if (consp entries)
      (+
       (nth 2 (car entries))
       (putnam-2000-b3-total-multiplicity
        (cdr entries)))
    0))

;; The existential list is only a finite presentation of the source's root
;; set, not a choice of its cardinality. ROOT-ENTRIES-P admits no duplicate
;; point, ALL-ROOTS-LISTED-P makes the list complete, and MULTIPLICITY-P fixes
;; the unique first derivative order that is nonzero at each point. Hence any
;; two exact root lists differ only in ordering and have the same total.

(defun-sk putnam-2000-b3-root-count-is-p
    (coefficients derivative-order count zero one)
  (exists (entries)
    (and
     (natp count)
     (putnam-2000-b3-exact-root-list-p
      entries coefficients derivative-order zero one)
     (equal
      (putnam-2000-b3-total-multiplicity entries)
      count))))

(defun-sk putnam-2000-b3-count-comparison-p
    (coefficients i j zero one)
  (exists (count-i count-j)
    (and
     (putnam-2000-b3-root-count-is-p
      coefficients i count-i zero one)
     (putnam-2000-b3-root-count-is-p
      coefficients j count-j zero one)
     (<= count-i count-j))))

(defun-sk putnam-2000-b3-nondecreasing-p
    (coefficients zero one)
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i j))
     (putnam-2000-b3-count-comparison-p
      coefficients i j zero one))))

(defun-sk putnam-2000-b3-tail-equals-twice-frequency-p
    (coefficients cutoff zero one)
  (forall (k)
    (implies
     (and
      (natp k)
      (<= cutoff k))
     (putnam-2000-b3-root-count-is-p
      coefficients
      k
      (* 2 (len coefficients))
      zero one))))

(defun-sk putnam-2000-b3-eventually-twice-frequency-p
    (coefficients zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2000-b3-tail-equals-twice-frequency-p
      coefficients cutoff zero one))))

;; The coefficient list is (a_1,...,a_N), so its nonempty length is N and its
;; last entry is the source assumption a_N != 0. The half-open interval [0,1)
;; maps bijectively to the unit circle by t |-> (cos(2*pi*t),sin(2*pi*t)).
;; Exact duplicate-free root lists therefore define the same M(k) internally.
;; Since M is natural-valued, convergence to 2N is equivalent to eventual
;; equality with 2N.
;;
;; The real-field antecedent is a structure hypothesis on ACL2's arbitrary
;; defstub operations, not an existentially chosen witness. The resulting
;; implication is uniform over every interpretation satisfying the laws, and
;; the ordinary real numbers supply a concrete satisfying interpretation.

(defun putnambench-putnam-2000-b3-statement
    (coefficients zero one)
  (implies
   (and
    (putnam-2000-b3-real-field-p zero one)
    (true-listp coefficients)
    (consp coefficients)
    (putnam-2000-b3-coefficient-list-p coefficients)
    (not
     (equal (car (last coefficients)) zero)))
   (and
    (putnam-2000-b3-nondecreasing-p
     coefficients zero one)
    (putnam-2000-b3-eventually-twice-frequency-p
     coefficients zero one))))

(value-triple :itpeval-statement-checked)
:q
