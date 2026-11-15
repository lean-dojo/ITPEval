;; Statement-only formalization of thousand-theorems corpus artifact Q282649,
;; "Pentagonal number theorem": over every commutative ring, the formal
;; power-series product of (1 - X^(n+1)) has the generalized-pentagonal
;; coefficients with alternating signs. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A carrier identifier and conservative operation interfaces present an
;; arbitrary commutative ring. Every ring law used by the source type class is
;; explicit in the statement predicate; the carrier is neither enumerated nor
;; restricted to ACL2's built-in numeric domains.

(defstub q282649-member-p (ring value) t)
(defstub q282649-zero (ring) t)
(defstub q282649-one (ring) t)
(defstub q282649-add (ring left right) t)
(defstub q282649-multiply (ring left right) t)
(defstub q282649-negate (ring value) t)

(defun-sk q282649-commutative-ring-laws-p (ring)
  (forall (x y z)
    (implies
     (and
      (q282649-member-p ring x)
      (q282649-member-p ring y)
      (q282649-member-p ring z))
     (let ((xy-add (q282649-add ring x y))
           (yz-add (q282649-add ring y z))
           (xy-multiply (q282649-multiply ring x y))
           (yz-multiply (q282649-multiply ring y z)))
       (and
        (q282649-member-p ring (q282649-negate ring x))
        (q282649-member-p ring xy-add)
        (q282649-member-p ring xy-multiply)
        (equal
         (q282649-add ring xy-add z)
         (q282649-add ring x yz-add))
        (equal xy-add (q282649-add ring y x))
        (equal (q282649-add ring x (q282649-zero ring)) x)
        (equal
         (q282649-add ring x (q282649-negate ring x))
         (q282649-zero ring))
        (equal
         (q282649-multiply ring xy-multiply z)
         (q282649-multiply ring x yz-multiply))
        (equal xy-multiply (q282649-multiply ring y x))
        (equal (q282649-multiply ring x (q282649-one ring)) x)
        (equal
         (q282649-multiply ring x yz-add)
         (q282649-add
          ring
          (q282649-multiply ring x y)
          (q282649-multiply ring x z))))))))

(defun q282649-commutative-ring-p (ring)
  (and
   (q282649-member-p ring (q282649-zero ring))
   (q282649-member-p ring (q282649-one ring))
   (q282649-commutative-ring-laws-p ring)))

;; The generalized pentagonal number indexed by an integer k is
;; k(3k-1)/2. The product is always even, so this exact ACL2 rational
;; expression is an integer and agrees with Mathlib's natural-valued map.

(defun q282649-pentagonal (k)
  (if (integerp k)
      (/ (* k (- (* 3 k) 1)) 2)
    0))

(defun-sk q282649-pentagonal-index-exists-p (degree)
  (exists (k)
    (and
     (integerp k)
     (equal (q282649-pentagonal k) degree))))

(defchoose q282649-pentagonal-index
    (k)
    (degree)
  (and
   (integerp k)
   (equal (q282649-pentagonal k) degree)))

(defun q282649-neg-one-pow (ring k)
  (if (evenp k)
      (q282649-one ring)
    (q282649-negate ring (q282649-one ring))))

(defun q282649-pentagonal-series-coefficient (ring degree)
  (if (q282649-pentagonal-index-exists-p degree)
      (q282649-neg-one-pow
       ring
       (q282649-pentagonal-index degree))
    (q282649-zero ring)))

;; Duplicate-free natural lists are exact representatives of finite subsets
;; of N. The recursive coefficient is the coefficient of the finite product
;; over that set. Multiplication by (1 - X^(n+1)) sends coefficient d to
;; old(d) - old(d-(n+1)), which is exact formal-power-series convolution.

(defun q282649-all-natural-p (values)
  (if (endp values)
      t
    (and
     (natp (car values))
     (q282649-all-natural-p (cdr values)))))

(defun q282649-finite-natural-set-p (values)
  (and
   (true-listp values)
   (q282649-all-natural-p values)
   (no-duplicatesp-equal values)))

(defun q282649-finite-product-coefficient (ring finite-set degree)
  (declare (xargs :measure (acl2-count finite-set)))
  (if (endp finite-set)
      (if (equal degree 0)
          (q282649-one ring)
        (q282649-zero ring))
    (let* ((factor-degree (+ 1 (car finite-set)))
           (remaining-coefficient
            (q282649-finite-product-coefficient
             ring (cdr finite-set) degree)))
      (if (<= factor-degree degree)
          (q282649-add
           ring
           remaining-coefficient
           (q282649-negate
            ring
            (q282649-finite-product-coefficient
             ring
             (cdr finite-set)
             (- degree factor-degree))))
        remaining-coefficient))))

(defun-sk q282649-eventually-correct-at-cutoff-p
    (ring degree cutoff)
  (forall (finite-set)
    (implies
     (and
      (q282649-finite-natural-set-p finite-set)
      (subsetp-equal cutoff finite-set))
     (equal
      (q282649-finite-product-coefficient
       ring finite-set degree)
      (q282649-pentagonal-series-coefficient
       ring degree)))))

(defun-sk q282649-coefficient-cutoff-exists-p (ring degree)
  (exists (cutoff)
    (and
     (q282649-finite-natural-set-p cutoff)
     (q282649-eventually-correct-at-cutoff-p
      ring degree cutoff))))

;; The source HasProd assertion is polymorphic over every topology on the
;; coefficient ring. In the coefficientwise topology, eventual equality of
;; each coefficient implies convergence for every topology. Conversely,
;; specializing that universal source assertion to the discrete coefficient
;; topology yields exactly this coefficientwise eventual-equality predicate.
;; Thus the following universal closure is bidirectionally equivalent to the
;; source statement, while avoiding any finite or weaker model of topology.

(defun-sk thousand-theorems-q282649-pentagonal-number-theorem-statement ()
  (forall (ring degree)
    (implies
     (and
      (q282649-commutative-ring-p ring)
      (natp degree))
     (q282649-coefficient-cutoff-exists-p
      ring degree))))

(value-triple :itpeval-statement-checked)
:q
