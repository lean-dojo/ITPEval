;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_poke_8bitqtvc: the 8-bit bitwalker poke
;; verification condition, preserving every non-target bit while setting the
;; selected bit to a Boolean flag. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source's unsigned
;; fixed-width bit vectors.

(defun poke8-bv8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun poke8-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun poke8-bv8-truncate (value)
  (mod value 256))

(defun poke8-bv8-sub (left right)
  (mod (- left right) 256))

(defun poke8-bv32-sub (left right)
  (mod (- left right) 4294967296))

(defun poke8-bv8-or (left right)
  (mod (logior left right) 256))

(defun poke8-bv8-not (value)
  (mod (lognot value) 256))

(defun poke8-bv8-and (left right)
  (mod (logand left right) 256))

;; BitVec.getElem! returns false outside the word. Since represented words are
;; nonnegative, logbitp gives exactly the source Boolean bit value.

(defun poke8-bit (word index)
  (logbitp (nfix index) word))

;; This is the unsigned representative of the 8-bit word obtained by shifting
;; one left by the source 8-bit position.

(defun poke8-single-bit-mask (position)
  (mod (ash 1 (nfix position)) 256))

;; Preserve the source quantification over every 32-bit index: result and byte
;; agree at all positions other than the modular 32-bit word 7 - left1.

(defun-sk poke8-equal-except-bv32-p
    (result byte left1)
  (forall (index)
    (implies
     (poke8-bv32-p index)
     (implies
      (< index 8)
      (implies
       (not
        (equal
         index
         (poke8-bv32-sub 7 left1)))
       (equal
        (poke8-bit
         result
         (poke8-bv8-truncate index))
        (poke8-bit
         byte
         (poke8-bv8-truncate index))))))))

(defun poke8-word-postcondition-p
    (result byte left1 flag)
  (and
   (poke8-equal-except-bv32-p
    result byte left1)
   (equal
    (poke8-bit
     result
     (poke8-bv8-sub
      7
      (poke8-bv8-truncate left1)))
    flag)))

;; For each 8-bit result, the source update equation implies the word-indexed
;; postcondition. Boolean true selects OR; false selects AND with the
;; fixed-width complement of the one-bit mask.

(defun-sk poke8-all-updated-results-p
    (left1 flag byte mask)
  (forall (result)
    (implies
     (poke8-bv8-p result)
     (implies
      (equal
       result
       (if flag
           (poke8-bv8-or byte mask)
         (poke8-bv8-and
          byte
          (poke8-bv8-not mask))))
      (poke8-word-postcondition-p
       result byte left1 flag)))))

;; Preserve the source quantification over every mathematical integer in the
;; final, integer-indexed version of non-target-bit preservation.

(defun-sk poke8-equal-except-int-p
    (result byte left1)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index 8))
      (implies
       (not
        (equal index (- 7 left1)))
       (equal
        (poke8-bit result index)
        (poke8-bit byte index)))))))

(defun poke8-integer-postcondition-p
    (result byte left1 flag)
  (and
   (poke8-equal-except-int-p
    result byte left1)
   (equal
    (poke8-bit result (- 7 left1))
    flag)))

;; Every source-typed result satisfying the bit-vector-indexed postcondition
;; must satisfy its integer-indexed counterpart.

(defun-sk poke8-all-postcondition-results-p
    (left1 flag byte)
  (forall (result)
    (implies
     (poke8-bv8-p result)
     (implies
      (poke8-word-postcondition-p
       result byte left1 flag)
      (poke8-integer-postcondition-p
       result byte left1 flag)))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-poke-8bitqtvc-statement
    (left1 flag byte)
  (implies
   (and
    (poke8-bv32-p left1)
    (booleanp flag)
    (poke8-bv8-p byte)
    (< left1 8))
   (let ((o1 (poke8-bv8-truncate left1)))
     (and
      (and
       (or
        (<= o1 7)
        (<= o1 7))
       (let ((o2 (poke8-bv8-sub 7 o1)))
         (implies
          (equal o2 (- 7 o1))
          (let ((mask (poke8-single-bit-mask o2)))
            (and
             (if flag t t)
             (poke8-all-updated-results-p
              left1 flag byte mask))))))
      (poke8-all-postcondition-results-p
       left1 flag byte)))))

(value-triple :itpeval-statement-checked)
:q
