;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_poke_64bit_bvqtvc: the 64-bit bitwalker poke
;; verification condition, preserving every non-target bit while setting the
;; selected bit to a Boolean flag. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source's unsigned
;; fixed-width bit vectors.

(defun poke64-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun poke64-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun poke64-bv32-sub (left right)
  (mod (- left right) 4294967296))

;; BitVec.getElem! returns false outside the word. Since all represented words
;; are nonnegative, logbitp gives exactly the source Boolean bit value.

(defun poke64-bit (word index)
  (logbitp (nfix index) word))

;; This is the unsigned representative of the 64-bit word obtained by shifting
;; one left by the zero-extended 32-bit position.

(defun poke64-single-bit-mask (position)
  (if (< (nfix position) 64)
      (ash 1 (nfix position))
    0))

;; Preserve the source quantification over every 32-bit index: result and value
;; agree at all positions other than 63 - left1.

(defun-sk poke64-equal-except-bv32-p
    (result value left1)
  (forall (index)
    (implies
     (poke64-bv32-p index)
     (implies
      (not
       (equal
        index
        (poke64-bv32-sub 63 left1)))
      (equal
       (poke64-bit result index)
       (poke64-bit value index))))))

(defun poke64-word-postcondition-p
    (result value left1 flag)
  (let ((target (poke64-bv32-sub 63 left1)))
    (and
     (poke64-equal-except-bv32-p result value left1)
     (equal flag (poke64-bit result target)))))

;; For each 64-bit result, the source update equation implies the word-level
;; postcondition. Boolean true selects OR; false selects AND with the
;; fixed-width complement of the one-bit mask.

(defun-sk poke64-all-updated-results-p
    (left1 flag value mask)
  (forall (result)
    (implies
     (poke64-bv64-p result)
     (implies
      (equal
       result
       (if flag
           (logior value mask)
         (logand value (lognot mask))))
      (poke64-word-postcondition-p
       result value left1 flag)))))

;; Preserve the source quantification over every mathematical integer in the
;; final, integer-indexed version of non-target-bit preservation.

(defun-sk poke64-equal-except-int-p
    (result value left1)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (and
        (<= 0 index)
        (< index 64))
       (not
        (equal index (- 63 left1))))
      (equal
       (poke64-bit result index)
       (poke64-bit value index))))))

(defun poke64-integer-postcondition-p
    (result value left1 flag)
  (and
   (poke64-equal-except-int-p result value left1)
   (equal
    flag
    (poke64-bit result (- 63 left1)))))

;; Every source-typed result satisfying the bit-vector-indexed postcondition
;; must satisfy its integer-indexed counterpart.

(defun-sk poke64-all-postcondition-results-p
    (left1 flag value)
  (forall (result)
    (implies
     (poke64-bv64-p result)
     (implies
      (poke64-word-postcondition-p
       result value left1 flag)
      (poke64-integer-postcondition-p
       result value left1 flag)))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-poke-64bit-bvqtvc-statement
    (left1 flag value)
  (implies
   (and
    (poke64-bv32-p left1)
    (booleanp flag)
    (poke64-bv64-p value)
    (< left1 64))
   (and
    (or
     (<= left1 63)
     (<= left1 63))
    (let ((o1 (poke64-bv32-sub 63 left1)))
      (implies
       (equal o1 (- 63 left1))
       (let ((mask (poke64-single-bit-mask o1)))
         (and
          (if flag t t)
          (poke64-all-updated-results-p
           left1 flag value mask)))))
    (poke64-all-postcondition-results-p
     left1 flag value))))

(value-triple :itpeval-statement-checked)
:q
