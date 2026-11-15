;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/queens_bv_Bits_rightmost_bit_trickqtvc: the 32-bit rightmost-set-bit
;; verification condition, relating bitwise x AND -x to the singleton minimum
;; set bit and preserving the result-record postcondition. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with the source's 32-bit words.

(defun rightmost-bit-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Why3 finite sets of integers are represented by their unique strictly
;; increasing list of elements. This is a canonical, lossless encoding rather
;; than a restriction of the finite-set domain.

(defun rightmost-bit-increasing-tail-p (lower set)
  (if (consp set)
      (and
       (integerp (car set))
       (< lower (car set))
       (rightmost-bit-increasing-tail-p
        (car set)
        (cdr set)))
    (equal set nil)))

(defun rightmost-bit-int-fset-p (set)
  (if (consp set)
      (and
       (integerp (car set))
       (rightmost-bit-increasing-tail-p
        (car set)
        (cdr set)))
    (equal set nil)))

(defun rightmost-bit-member-p (value set)
  (if (member-equal value set) t nil))

(defun rightmost-bit-min-elt (set)
  (if (consp set)
      (car set)
    0))

;; A source Bits.t record is represented by (BV . MDL). Canonical finite-set
;; representation makes component equality coincide with source record
;; equality, and the predicate below retains the complete type invariant.

(defun rightmost-bit-bv (object)
  (car object))

(defun rightmost-bit-mdl (object)
  (cdr object))

(defun-sk rightmost-bit-record-invariant-p (word model)
  (forall (index)
    (implies
     (integerp index)
     (iff
      (and
       (<= 0 index)
       (< index 32)
       (logbitp (nfix index) word))
      (rightmost-bit-member-p index model)))))

(defun rightmost-bit-t-p (object)
  (and
   (consp object)
   (rightmost-bit-bv32-p
    (rightmost-bit-bv object))
   (rightmost-bit-int-fset-p
    (rightmost-bit-mdl object))
   (rightmost-bit-record-invariant-p
    (rightmost-bit-bv object)
    (rightmost-bit-mdl object))))

;; BV32 negation is modular negation. Both operands of LOGAND are therefore
;; the unsigned representatives of the corresponding source words.

(defun rightmost-bit-neg32 (word)
  (mod (- word) 4294967296))

(defun rightmost-bit-result-word (word)
  (logand word (rightmost-bit-neg32 word)))

;; Preserve the source universal quantifier over every result record. The
;; premise and conclusion deliberately retain the generated VC's second
;; conjunct even though its model equality is immediate from the premise.

(defun-sk rightmost-bit-all-results-p
    (result-word singleton-model)
  (forall (result)
    (implies
     (rightmost-bit-t-p result)
     (implies
      (and
       (equal
        (rightmost-bit-bv result)
        result-word)
       (equal
        (rightmost-bit-mdl result)
        singleton-model))
      (equal
       (rightmost-bit-mdl result)
       singleton-model)))))

(defun
  ntp4vc-pearl-queens-bv-bits-rightmost-bit-trickqtvc-statement
  (a)
  (implies
   (rightmost-bit-t-p a)
   (implies
    (not (equal (rightmost-bit-mdl a) nil))
    (let* ((result-word
            (rightmost-bit-result-word
             (rightmost-bit-bv a)))
           (singleton-model
            (list
             (rightmost-bit-min-elt
              (rightmost-bit-mdl a)))))
      (and
       (rightmost-bit-record-invariant-p
        result-word
        singleton-model)
       (rightmost-bit-all-results-p
        result-word
        singleton-model))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
