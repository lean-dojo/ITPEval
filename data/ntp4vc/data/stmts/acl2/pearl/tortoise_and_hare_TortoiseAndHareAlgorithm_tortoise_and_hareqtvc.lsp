;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hareqtvc:
;; the Floyd tortoise-and-hare algorithm verification condition for an
;; integer-valued iteration on a finite interval, including both loop
;; invariants and the returned cycle parameters. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the arbitrary integer function, interval
;; bound, initial value, and its iterated sequence.

(defstub tah-f (value) t)
(defstub tah-m () t)
(defstub tah-x0 () t)
(defstub tah-x (index) t)

;; Preserve the source function types over all mathematical integers.

(defun-sk tah-function-types-p ()
  (forall (value index)
    (and
     (implies
      (integerp value)
      (integerp (tah-f value)))
     (implies
      (integerp index)
      (integerp (tah-x index))))))

;; The source axiom that f maps the interval [0,m) into itself.

(defun-sk tah-f-range-p ()
  (forall (value)
    (implies
     (integerp value)
     (implies
      (and
       (<= 0 value)
       (< value (tah-m)))
      (and
       (<= 0 (tah-f value))
       (< (tah-f value) (tah-m)))))))

;; This is the nonnegative part of x(i) = iter f i x0 used by the
;; verification condition. The Why3 iteration equations give x(0) = x0 and
;; x(k) = f(x(k-1)) for every positive integer k.

(defun-sk tah-positive-iteration-p ()
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< 0 index)
      (equal
       (tah-x index)
       (tah-f (tah-x (- index 1))))))))

(defun tah-iteration-p ()
  (and
   (equal (tah-x 0) (tah-x0))
   (tah-positive-iteration-p)))

;; Quantified sequence-distinctness predicates occurring in the hypotheses
;; and loop invariants.

(defun-sk tah-no-repeat-before-p (bound)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right))
     (implies
      (and
       (<= 0 left)
       (< left right)
       (< right bound))
      (not
       (equal
        (tah-x left)
        (tah-x right)))))))

(defun-sk tah-no-tortoise-hare-before-p (bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 1 index)
       (< index bound))
      (not
       (equal
        (tah-x index)
        (tah-x (* 2 index))))))))

(defun-sk tah-aligned-prefix-distinct-p (n bound)
  (forall (offset)
    (implies
     (integerp offset)
     (implies
      (and
       (<= 0 offset)
       (< offset bound))
      (not
       (equal
        (tah-x offset)
        (tah-x (+ n offset))))))))

(defun-sk tah-positive-offsets-distinct-p (n bound)
  (forall (offset)
    (implies
     (integerp offset)
     (implies
      (and
       (< 0 offset)
       (< offset bound))
      (not
       (equal
        (tah-x (+ n offset))
        (tah-x n)))))))

;; Common preservation facts after one iteration of the second loop.

(defun tah-second-loop-step-p (mu n i)
  (and
   (and
    (<= 0 (- mu i))
    (< (- mu (+ i 1))
       (- mu i)))
   (and
    (<= 0 (+ i 1))
    (<= (+ i 1) mu))
   (and
    (equal
     (tah-f (tah-x i))
     (tah-x (+ i 1)))
    (equal
     (tah-f (tah-x (+ n i)))
     (tah-x (+ n (+ i 1)))))
   (tah-aligned-prefix-distinct-p
    n
    (+ i 1))))

;; The second loop's exit branch universally quantifies the selected period.

(defun tah-final-cycle-parameters-p (i l)
  (and
   (and
    (<= 0 i)
    (< i (tah-m)))
   (and
    (<= 1 l)
    (<= l (tah-m)))
   (<= (+ i l) (tah-m))
   (equal
    (tah-x (+ i l))
    (tah-x i))
   (tah-no-repeat-before-p (+ i l))))

(defun-sk tah-all-final-periods-p (n lam i)
  (forall (period)
    (implies
     (integerp period)
     (implies
      (if (equal lam 0)
          (equal period n)
        (equal period lam))
      (tah-final-cycle-parameters-p
       i
       period)))))

;; This preserves the internal universal Boolean temporary o1. ACL2's t and
;; nil are the two source Boolean values.

(defun tah-o1-assignment (n lam i)
  (if (equal lam 0)
      (if (< 0 i)
          (if (equal
               (tah-x (+ n i))
               (tah-x n))
              t
            nil)
        nil)
    nil))

(defun tah-o1-true-branch-p (mu lambda n i)
  (and
   (tah-second-loop-step-p mu n i)
   (if (equal i 0)
       (tah-positive-offsets-distinct-p
        n
        (+ i 1))
     (equal i lambda))))

(defun tah-o1-false-branch-p (mu lambda n lam i)
  (and
   (tah-second-loop-step-p mu n i)
   (if (equal lam 0)
       (tah-positive-offsets-distinct-p
        n
        (+ i 1))
     (equal lam lambda))))

(defun-sk tah-all-o1-cases-p (mu lambda n lam i)
  (forall (o1)
    (implies
     (booleanp o1)
     (implies
      (equal
       o1
       (tah-o1-assignment n lam i))
      (if (equal o1 t)
          (tah-o1-true-branch-p
           mu lambda n i)
        (tah-o1-false-branch-p
         mu lambda n lam i))))))

;; The complete second-loop preservation/exit obligation for fixed n.

(defun tah-second-loop-case-p (mu lambda n lam i)
  (implies
   (and
    (and
     (<= 0 i)
     (<= i mu))
    (tah-aligned-prefix-distinct-p n i)
    (if (equal lam 0)
        (tah-positive-offsets-distinct-p n i)
      (equal lam lambda)))
   (if (not
        (equal
         (tah-x i)
         (tah-x (+ n i))))
       (tah-all-o1-cases-p
        mu lambda n lam i)
     (tah-all-final-periods-p
      n lam i))))

(defun-sk tah-all-second-loop-cases-p (mu lambda n)
  (forall (lam i)
    (implies
     (and
      (integerp lam)
      (integerp i))
     (tah-second-loop-case-p
      mu lambda n lam i))))

;; Initial facts and the complete continuation obligation for the second loop
;; after the first loop has found an equality x(n) = x(2*n).

(defun tah-second-loop-conclusion-p (mu lambda n)
  (and
   (and
    (and
     (<= 0 0)
     (<= 0 mu))
    (and
     (equal (tah-x0) (tah-x 0))
     (equal
      (tah-x n)
      (tah-x (+ n 0))))
    (tah-aligned-prefix-distinct-p n 0)
    (tah-positive-offsets-distinct-p n 0))
   (tah-all-second-loop-cases-p
    mu
    lambda
    n)))

;; Preservation of the first loop when its current values are unequal.

(defun tah-first-loop-step-p (mu lambda n)
  (and
   (not
    (< (+ mu lambda)
       (+ n 1)))
   (implies
    (not
     (< (+ mu lambda)
        (+ n 1)))
    (and
     (and
      (<= 0 (- (+ mu lambda) n))
      (< (- (+ mu lambda) (+ n 1))
         (- (+ mu lambda) n)))
     (and
      (<= 1 (+ n 1))
      (<= (+ n 1) (+ mu lambda)))
     (equal
      (tah-f (tah-x n))
      (tah-x (+ n 1)))
     (equal
      (tah-f
       (tah-f
        (tah-x (* 2 n))))
      (tah-x (* 2 (+ n 1))))
     (tah-no-tortoise-hare-before-p
      (+ n 1))))))

(defun tah-first-loop-case-p (mu lambda n)
  (implies
   (and
    (and
     (<= 1 n)
     (<= n (+ mu lambda)))
    (tah-no-tortoise-hare-before-p n))
   (if (not
        (equal
         (tah-x n)
         (tah-x (* 2 n))))
       (tah-first-loop-step-p
        mu lambda n)
     (tah-second-loop-conclusion-p
      mu lambda n))))

(defun-sk tah-all-first-loop-cases-p (mu lambda)
  (forall (n)
    (implies
     (integerp n)
     (tah-first-loop-case-p
      mu lambda n))))

;; The complete VC conclusion, including the deliberately redundant and
;; vacuous initialization conjuncts generated from the program.

(defun tah-vc-conclusion-p (mu lambda)
  (and
   (<= 1 1)
   (<= 1 (+ mu lambda))
   (equal
    (tah-f (tah-x0))
    (tah-x 1))
   (equal
    (tah-f (tah-f (tah-x0)))
    (tah-x (* 2 1)))
   (tah-no-tortoise-hare-before-p 1)
   (tah-all-first-loop-cases-p
    mu lambda)))

;; The outer quantifiers, source typing and axioms, periodicity hypotheses,
;; and full generated conclusion are all retained in the statement predicate.

(defun-sk
  ntp4vc-pearl-tortoise-and-hare-tortoise-and-hareqtvc-statement
  ()
  (forall (mu lambda)
    (implies
     (and
      (integerp mu)
      (integerp lambda)
      (integerp (tah-m))
      (integerp (tah-x0))
      (tah-function-types-p)
      (< 0 (tah-m))
      (tah-f-range-p)
      (<= 0 (tah-x0))
      (< (tah-x0) (tah-m))
      (tah-iteration-p))
     (implies
      (and
       (<= 0 mu)
       (< mu (tah-m))
       (<= 1 lambda)
       (<= lambda (tah-m))
       (<= (+ mu lambda) (tah-m))
       (equal
        (tah-x (+ mu lambda))
        (tah-x mu))
       (tah-no-repeat-before-p
        (+ mu lambda)))
      (tah-vc-conclusion-p
       mu lambda)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
