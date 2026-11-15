;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a4:
;; under the interval-length product bound, the integers in A whose
;; r-multiples are congruent modulo q to an integer in B form a finite
;; arithmetic progression. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's conservative generic symbols present an arbitrary Archimedean
;; ordered field and its integer embedding. Completeness is not used by this
;; theorem; Archimedeanness is the exact property ensuring that bounded real
;; intervals contain only finitely many embedded integers.

(defstub p12a4-scalar-p (x) t)
(defstub p12a4-add (x y) t)
(defstub p12a4-multiply (x y) t)
(defstub p12a4-negate (x) t)
(defstub p12a4-less (x y) t)
(defstub p12a4-integer-embed (n) t)
(defstub p12a4-archimedean-bound (x) t)

(defun p12a4-member-p (x)
  (if (p12a4-scalar-p x) t nil))

(defun p12a4-less-p (x y)
  (if (p12a4-less x y) t nil))

(defun p12a4-subtract (x y)
  (p12a4-add x (p12a4-negate y)))

(defun p12a4-in-closed-interval-p (lower upper x)
  (and
   (not (p12a4-less-p x lower))
   (not (p12a4-less-p upper x))))

(defun-sk p12a4-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p12a4-member-p x)
      (p12a4-member-p y)
      (p12a4-member-p z))
     (and
      (p12a4-member-p (p12a4-add x y))
      (p12a4-member-p (p12a4-multiply x y))
      (p12a4-member-p (p12a4-negate x))
      (equal
       (p12a4-add (p12a4-add x y) z)
       (p12a4-add x (p12a4-add y z)))
      (equal (p12a4-add x y) (p12a4-add y x))
      (equal (p12a4-add x zero) x)
      (equal (p12a4-add x (p12a4-negate x)) zero)
      (equal
       (p12a4-multiply (p12a4-multiply x y) z)
       (p12a4-multiply x (p12a4-multiply y z)))
      (equal (p12a4-multiply x y) (p12a4-multiply y x))
      (equal (p12a4-multiply x one) x)
      (equal
       (p12a4-multiply x (p12a4-add y z))
       (p12a4-add
        (p12a4-multiply x y)
        (p12a4-multiply x z)))))))

(defun-sk p12a4-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p12a4-member-p x)
      (p12a4-member-p y)
      (p12a4-member-p z))
     (and
      (not (p12a4-less-p x x))
      (or
       (equal x y)
       (p12a4-less-p x y)
       (p12a4-less-p y x))
      (implies
       (and
        (p12a4-less-p x y)
        (p12a4-less-p y z))
       (p12a4-less-p x z))
      (implies
       (p12a4-less-p x y)
       (p12a4-less-p
        (p12a4-add x z)
        (p12a4-add y z)))
      (implies
       (and
        (p12a4-less-p zero x)
        (p12a4-less-p zero y))
       (p12a4-less-p
        zero
        (p12a4-multiply x y)))))))

(defun-sk p12a4-integer-embedding-laws-p ()
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (p12a4-member-p (p12a4-integer-embed m))
      (equal
       (p12a4-integer-embed (+ m n))
       (p12a4-add
        (p12a4-integer-embed m)
        (p12a4-integer-embed n)))
      (equal
       (p12a4-integer-embed (* m n))
       (p12a4-multiply
        (p12a4-integer-embed m)
        (p12a4-integer-embed n)))
      (iff
       (< m n)
       (p12a4-less-p
        (p12a4-integer-embed m)
        (p12a4-integer-embed n)))))))

(defun-sk p12a4-archimedean-law-p ()
  (forall (x)
    (implies
     (p12a4-member-p x)
     (and
      (integerp (p12a4-archimedean-bound x))
      (p12a4-less-p
       x
       (p12a4-integer-embed
        (p12a4-archimedean-bound x)))))))

(defun p12a4-archimedean-ordered-field-p (zero one)
  (and
   (p12a4-member-p zero)
   (p12a4-member-p one)
   (not (equal zero one))
   (p12a4-ring-laws-p zero one)
   (p12a4-order-laws-p zero)
   (p12a4-less-p zero one)
   (equal (p12a4-integer-embed 0) zero)
   (equal (p12a4-integer-embed 1) one)
   (p12a4-integer-embedding-laws-p)
   (p12a4-archimedean-law-p)))

(defun-sk p12a4-t-member-p
    (b-lower b-upper q x)
  (exists (b m)
    (and
     (integerp b)
     (integerp m)
     (p12a4-in-closed-interval-p
      b-lower b-upper
      (p12a4-integer-embed b))
     (equal x (+ b (* m q))))))

(defun p12a4-s-member-p
    (a-lower a-upper b-lower b-upper q r x)
  (and
   (integerp x)
   (p12a4-in-closed-interval-p
    a-lower a-upper
    (p12a4-integer-embed x))
   (p12a4-t-member-p
    b-lower b-upper q (* r x))))

(defun-sk p12a4-progression-member-p
    (x n start step)
  (exists (i)
    (and
     (natp i)
     (< i n)
     (equal x (+ start (* i step))))))

(defun-sk p12a4-s-is-progression-p
    (a-lower a-upper b-lower b-upper q r n start step)
  (forall (x)
    (implies
     (integerp x)
     (iff
      (p12a4-s-member-p
       a-lower a-upper b-lower b-upper q r x)
      (p12a4-progression-member-p
       x n start step)))))

(defun-sk p12a4-finite-progression-exists-p
    (a-lower a-upper b-lower b-upper q r)
  (exists (n start step)
    (and
     (natp n)
     (integerp start)
     (integerp step)
     (< 0 step)
     (p12a4-s-is-progression-p
      a-lower a-upper b-lower b-upper q r
      n start step))))

(defun putnambench-putnam-2012-a4-statement
    (zero one q r a-lower a-upper b-lower b-upper)
  (let* ((a-length
          (p12a4-subtract a-upper a-lower))
         (b-length
          (p12a4-subtract b-upper b-lower))
         (length-product
          (p12a4-multiply a-length b-length)))
    (implies
     (and
      (p12a4-archimedean-ordered-field-p zero one)
      (integerp q)
      (integerp r)
      (< 0 q)
      (p12a4-member-p a-lower)
      (p12a4-member-p a-upper)
      (p12a4-member-p b-lower)
      (p12a4-member-p b-upper)
      (p12a4-less-p a-lower a-upper)
      (p12a4-less-p b-lower b-upper)
      (p12a4-less-p
       length-product
       (p12a4-integer-embed q)))
     (p12a4-finite-progression-exists-p
      a-lower a-upper b-lower b-upper q r))))

(value-triple :itpeval-statement-checked)
:q
