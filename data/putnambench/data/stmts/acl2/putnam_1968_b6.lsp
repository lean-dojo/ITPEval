;; Statement-only formalization of PutnamBench corpus artifact putnam_1968_b6:
;; no sequence of compact subsets of the rationals is cofinal under inclusion
;; among all compact subsets of the rationals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets and set-valued sequences use the repository's tame APPLY$ function
;; objects. Compactness is represented by the equivalent sequential
;; compactness condition for the metric space of rational numbers.

(defun p68b6-member-p (set x)
  (if (apply$ set (list x)) t nil))

(defun p68b6-sequence-value (sequence n)
  (apply$ sequence (list n)))

(defun p68b6-family-set (family n)
  (apply$ family (list n)))

(defun-sk p68b6-set-values-rational-p (set)
  (forall (x)
    (implies
     (p68b6-member-p set x)
     (rationalp x))))

(defun p68b6-rational-set-p (set)
  (and
   (tamep-functionp set)
   (p68b6-set-values-rational-p set)))

(defun-sk p68b6-subset-values-p (left right)
  (forall (x)
    (implies
     (p68b6-member-p left x)
     (p68b6-member-p right x))))

(defun p68b6-subset-p (left right)
  (and
   (p68b6-rational-set-p left)
   (p68b6-rational-set-p right)
   (p68b6-subset-values-p left right)))

(defun-sk p68b6-sequence-values-in-set-p (set sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((value (p68b6-sequence-value sequence n)))
       (and
        (rationalp value)
        (p68b6-member-p set value))))))

(defun p68b6-sequence-in-set-p (set sequence)
  (and
   (p68b6-rational-set-p set)
   (tamep-functionp sequence)
   (p68b6-sequence-values-in-set-p set sequence)))

(defun-sk p68b6-subsequence-values-p (subsequence)
  (forall (m n)
    (and
     (implies
      (natp m)
      (natp (p68b6-sequence-value subsequence m)))
     (implies
      (and
       (natp m)
       (natp n)
       (< m n))
      (< (p68b6-sequence-value subsequence m)
         (p68b6-sequence-value subsequence n))))))

(defun p68b6-subsequence-p (subsequence)
  (and
   (tamep-functionp subsequence)
   (p68b6-subsequence-values-p subsequence)))

(defun-sk p68b6-convergence-tail-p
    (sequence subsequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (<
      (abs
       (-
        (p68b6-sequence-value
         sequence
         (p68b6-sequence-value subsequence n))
        limit))
      epsilon))))

(defun-sk p68b6-convergence-tail-exists-p
    (sequence subsequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p68b6-convergence-tail-p
      sequence subsequence limit epsilon cutoff))))

(defun-sk p68b6-converges-along-subsequence-p
    (sequence subsequence limit)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (p68b6-convergence-tail-exists-p
      sequence subsequence limit epsilon))))

(defun-sk p68b6-compact-sequence-witness-exists-p
    (set sequence)
  (exists (subsequence limit)
    (and
     (p68b6-subsequence-p subsequence)
     (rationalp limit)
     (p68b6-member-p set limit)
     (p68b6-converges-along-subsequence-p
      sequence subsequence limit))))

(defun-sk p68b6-every-sequence-has-compact-witness-p (set)
  (forall (sequence)
    (implies
     (p68b6-sequence-in-set-p set sequence)
     (p68b6-compact-sequence-witness-exists-p
      set sequence))))

(defun p68b6-compact-rational-set-p (set)
  (and
   (p68b6-rational-set-p set)
   (p68b6-every-sequence-has-compact-witness-p set)))

(defun-sk p68b6-family-values-compact-p (family)
  (forall (n)
    (implies
     (natp n)
     (p68b6-compact-rational-set-p
      (p68b6-family-set family n)))))

(defun-sk p68b6-family-contains-set-p (family set)
  (exists (n)
    (and
     (natp n)
     (p68b6-subset-p
      set
      (p68b6-family-set family n)))))

(defun-sk p68b6-family-cofinal-p (family)
  (forall (set)
    (implies
     (p68b6-compact-rational-set-p set)
     (p68b6-family-contains-set-p family set))))

(defun p68b6-compact-cofinal-family-p (family)
  (and
   (tamep-functionp family)
   (p68b6-family-values-compact-p family)
   (p68b6-family-cofinal-p family)))

(defun-sk p68b6-compact-cofinal-family-exists-p ()
  (exists (family)
    (p68b6-compact-cofinal-family-p family)))

(defun putnambench-putnam-1968-b6-statement ()
  (not (p68b6-compact-cofinal-family-exists-p)))

(value-triple :itpeval-statement-checked)
:q
