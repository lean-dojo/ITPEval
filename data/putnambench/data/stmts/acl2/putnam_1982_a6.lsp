;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_a6:
;; there is a decreasing-magnitude real series and a bijection satisfying the
;; stated displacement limit whose rearranged partial sums do not tend to one.
;; This file contains no proof.

(in-package "ACL2")

;; Standard ACL2's scalar domain is rational. A rational-valued counterexample
;; is also a real-valued counterexample, so it suffices for this disproof
;; problem. The witnesses remain internally existential: the statement does
;; not prescribe a particular sequence, permutation, or convergence modulus.

(defun putnam-1982-a6-value (function n)
  (apply$ function (list n)))

(defun-sk putnam-1982-a6-positive-integer-map-p (function)
  (forall (n)
    (implies
     (posp n)
     (posp (putnam-1982-a6-value function n)))))

(defun-sk putnam-1982-a6-inverse-laws-p
    (permutation inverse)
  (forall (n)
    (implies
     (posp n)
     (and
      (equal
       (putnam-1982-a6-value
        permutation
        (putnam-1982-a6-value inverse n))
       n)
      (equal
       (putnam-1982-a6-value
        inverse
        (putnam-1982-a6-value permutation n))
       n)))))

(defun putnam-1982-a6-bijection-p
    (permutation inverse)
  (and
   (tamep-functionp permutation)
   (tamep-functionp inverse)
   (putnam-1982-a6-positive-integer-map-p permutation)
   (putnam-1982-a6-positive-integer-map-p inverse)
   (putnam-1982-a6-inverse-laws-p permutation inverse)))

(defun-sk putnam-1982-a6-rational-sequence-p (sequence)
  (forall (n)
    (implies
     (posp n)
     (rationalp
      (putnam-1982-a6-value sequence n)))))

(defun-sk putnam-1982-a6-strictly-decreasing-magnitude-p
    (sequence)
  (forall (i j)
    (implies
     (and
      (posp i)
      (posp j)
      (< i j))
     (< (abs (putnam-1982-a6-value sequence j))
        (abs (putnam-1982-a6-value sequence i))))))

(defun putnam-1982-a6-prefix (sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (putnam-1982-a6-prefix sequence (- count 1))
       (putnam-1982-a6-value sequence count))))

(defun putnam-1982-a6-rearranged-prefix
    (permutation sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (putnam-1982-a6-rearranged-prefix
        permutation sequence (- count 1))
       (putnam-1982-a6-value
        sequence
        (putnam-1982-a6-value permutation count)))))

(defun-sk putnam-1982-a6-displacement-tail-p
    (permutation sequence epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (< (* (abs
            (- (putnam-1982-a6-value permutation n)
               n))
           (abs
            (putnam-1982-a6-value sequence n)))
        epsilon))))

(defun-sk putnam-1982-a6-displacement-cutoff-exists-p
    (permutation sequence epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1982-a6-displacement-tail-p
      permutation sequence epsilon cutoff))))

(defun-sk putnam-1982-a6-displacement-tends-to-zero-p
    (permutation sequence)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1982-a6-displacement-cutoff-exists-p
      permutation sequence epsilon))))

(defun-sk putnam-1982-a6-original-tail-p
    (sequence epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (< (abs
         (- (putnam-1982-a6-prefix sequence n)
            1))
        epsilon))))

(defun-sk putnam-1982-a6-original-cutoff-exists-p
    (sequence epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1982-a6-original-tail-p
      sequence epsilon cutoff))))

(defun-sk putnam-1982-a6-original-tends-to-one-p (sequence)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1982-a6-original-cutoff-exists-p
      sequence epsilon))))

(defun-sk putnam-1982-a6-rearranged-escape-exists-p
    (permutation sequence epsilon cutoff)
  (exists (n)
    (and
     (posp n)
     (<= cutoff n)
     (<= epsilon
         (abs
          (- (putnam-1982-a6-rearranged-prefix
              permutation sequence n)
             1))))))

(defun-sk putnam-1982-a6-rearranged-infinitely-often-away-p
    (permutation sequence epsilon)
  (forall (cutoff)
    (implies
     (natp cutoff)
     (putnam-1982-a6-rearranged-escape-exists-p
      permutation sequence epsilon cutoff))))

(defun-sk putnam-1982-a6-rearranged-not-tends-to-one-p
    (permutation sequence)
  (exists (epsilon)
    (and
     (rationalp epsilon)
     (< 0 epsilon)
     (putnam-1982-a6-rearranged-infinitely-often-away-p
      permutation sequence epsilon))))

(defun putnam-1982-a6-counterexample-p
    (permutation inverse sequence)
  (and
   (putnam-1982-a6-bijection-p permutation inverse)
   (tamep-functionp sequence)
   (putnam-1982-a6-rational-sequence-p sequence)
   (putnam-1982-a6-strictly-decreasing-magnitude-p sequence)
   (putnam-1982-a6-displacement-tends-to-zero-p
    permutation sequence)
   (putnam-1982-a6-original-tends-to-one-p sequence)
   (putnam-1982-a6-rearranged-not-tends-to-one-p
    permutation sequence)))

(defun-sk putnam-1982-a6-counterexample-exists-p ()
  (exists (permutation inverse sequence)
    (putnam-1982-a6-counterexample-p
     permutation inverse sequence)))

(defun putnambench-putnam-1982-a6-statement ()
  (putnam-1982-a6-counterexample-exists-p))

(value-triple :itpeval-statement-checked)
:q
