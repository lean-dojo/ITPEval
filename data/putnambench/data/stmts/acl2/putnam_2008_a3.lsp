;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_a3:
;; termination and choice-independent outcome of finite positive-integer
;; sequences under ordered gcd/lcm replacement. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A is the exact list representation of the source function Fin N -> Nat.
;; CHOICE is an arbitrary schedule function: at each natural time it returns
;; a proposed two-element list (J K). ACL2 functional instantiation makes the
;; theorem uniform over every such schedule. An illegal proposal means that
;; the corresponding source process does not satisfy TRANS, so that branch is
;; correctly vacuous.

(defstub putnam-2008-a3-choice (time) t)

(defun putnam-2008-a3-positive-list-p (values)
  (if (consp values)
      (and
       (posp (car values))
       (putnam-2008-a3-positive-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2008-a3-product (values)
  (if (consp values)
      (* (car values)
         (putnam-2008-a3-product (cdr values)))
    1))

(defun putnam-2008-a3-divides-p (divisor multiple)
  (and
   (posp divisor)
   (natp multiple)
   (equal (mod multiple divisor) 0)))

;; The decreasing candidate search is Euclid's gcd characterized directly as
;; the greatest positive common divisor, avoiding any additional library.

(defun putnam-2008-a3-gcd-through (left right candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      1
    (if (and
         (putnam-2008-a3-divides-p candidate left)
         (putnam-2008-a3-divides-p candidate right))
        candidate
      (putnam-2008-a3-gcd-through
       left right (- candidate 1)))))

(defun putnam-2008-a3-gcd (left right)
  (putnam-2008-a3-gcd-through
   left right (min (nfix left) (nfix right))))

(defun putnam-2008-a3-lcm (left right)
  (floor
   (* (nfix left) (nfix right))
   (putnam-2008-a3-gcd left right)))

(defun putnam-2008-a3-legal-pair-p (values n j k)
  (and
   (natp j)
   (natp k)
   (< j k)
   (< k n)
   (not
    (putnam-2008-a3-divides-p
     (nth j values)
     (nth k values)))))

;; SCAN-FUEL exceeds the number of ordered index pairs.  NIL means that the
;; state is terminal; otherwise the first legal pair is returned.

(defun putnam-2008-a3-first-legal-pair
    (values n j k scan-fuel)
  (declare (xargs :measure (nfix scan-fuel)))
  (cond
   ((zp scan-fuel) nil)
   ((not (< j n)) nil)
   ((not (< k n))
    (putnam-2008-a3-first-legal-pair
     values n (+ j 1) (+ j 2) (- scan-fuel 1)))
   ((putnam-2008-a3-legal-pair-p values n j k)
    (list j k))
   (t
    (putnam-2008-a3-first-legal-pair
     values n j (+ k 1) (- scan-fuel 1)))))

(defun putnam-2008-a3-find-legal-pair (values n)
  (putnam-2008-a3-first-legal-pair
   values n 0 1 (+ 1 (* n n))))

(defun putnam-2008-a3-step (values j k)
  (let* ((left (nth j values))
         (right (nth k values))
         (new-left (putnam-2008-a3-gcd left right))
         (new-right (putnam-2008-a3-lcm left right)))
    (update-nth
     k new-right
     (update-nth j new-left values))))

;; A legal move preserves the positive product.  Moreover, at the largest
;; changed index K its value strictly increases, since A_J does not divide
;; A_K.  Thus reverse lexicographic order strictly increases.  Every coordinate
;; stays between 1 and the initial product, so PRODUCT^N + 1 steps exceed every
;; possible legal path.

(defun putnam-2008-a3-canonical-final (values n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      values
    (let ((pair (putnam-2008-a3-find-legal-pair values n)))
      (if pair
          (putnam-2008-a3-canonical-final
           (putnam-2008-a3-step
            values (car pair) (cadr pair))
           n
           (- fuel 1))
        values))))

;; For a proposed time bound T, follow the arbitrary schedule for at most T
;; moves. Reaching TARGET in a terminal state succeeds. An illegal choice also
;; succeeds because that schedule does not encode a source process satisfying
;; TRANS. Exhausting T while a legal move remains fails.

(defun putnam-2008-a3-schedule-outcome-or-invalid-p
    (values n time fuel target)
  (declare (xargs :measure (nfix fuel)))
  (let ((pair (putnam-2008-a3-find-legal-pair values n)))
    (cond
     ((not pair)
      (equal values target))
     ((zp fuel) nil)
     (t
      (let ((choice (putnam-2008-a3-choice time)))
        (if
            (putnam-2008-a3-legal-pair-p
             values n (car choice) (cadr choice))
            (putnam-2008-a3-schedule-outcome-or-invalid-p
             (putnam-2008-a3-step
              values (car choice) (cadr choice))
             n
             (+ 1 (nfix time))
             (- fuel 1)
             target)
          t))))))

;; This is the source's unbounded existential stopping time. Its witness may
;; depend on the arbitrary schedule, exactly as the source's existential t is
;; nested under the universal process quantifier.

(defun-sk putnam-2008-a3-eventually-reaches-p
    (values n target)
  (exists
   (time)
   (and
    (natp time)
    (putnam-2008-a3-schedule-outcome-or-invalid-p
     values n 0 time target))))

(defun putnambench-putnam-2008-a3-statement (n a)
  (let* ((product (putnam-2008-a3-product a))
         (fuel (+ 1 (expt product n)))
         (target
          (putnam-2008-a3-canonical-final a n fuel)))
    (implies
     (and
      (posp n)
      (true-listp a)
      (equal (len a) n)
      (putnam-2008-a3-positive-list-p a))
     (and
      (not (putnam-2008-a3-find-legal-pair target n))
      (putnam-2008-a3-eventually-reaches-p
       a n target)))))

(value-triple :itpeval-statement-checked)
:q
