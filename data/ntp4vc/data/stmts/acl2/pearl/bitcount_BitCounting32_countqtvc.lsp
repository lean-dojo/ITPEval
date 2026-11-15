;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitcount_BitCounting32_countqtvc: the 32-bit parallel bit-counting
;; verification condition, including its five word updates and final relation
;; to the number of set bits. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with the source's 32-bit words.

(defun bc32-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value (expt 2 32))))

;; These operations are the source's unsigned 32-bit word operations.

(defun bc32-bv32-add (left right)
  (mod (+ left right) (expt 2 32)))

(defun bc32-bv32-sub (left right)
  (mod (- left right) (expt 2 32)))

(defun bc32-bv32-and (left right)
  (logand left right))

(defun bc32-bv32-shiftr (value amount)
  (ash value (- (nfix amount))))

;; The source nth_closure converts an integer index to a natural index and
;; reads that bit, returning false beyond the 32-bit word's high bit.

(defun bc32-nth-closure (value bit)
  (logbitp (nfix bit) value))

;; This is NumOf.numof specialized to nth_closure: it counts true values on
;; the half-open integer interval [lower, upper).

(defun bc32-numof-nth-closure (value lower upper)
  (declare
   (xargs
    :measure (nfix (- (ifix upper) (ifix lower)))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+ (if (bc32-nth-closure value (- upper 1)) 1 0)
         (bc32-numof-nth-closure value lower (- upper 1)))
    0))

(defun bc32-count-logic (value)
  (bc32-numof-nth-closure value 0 32))

;; Direct predicate encodings of the five source step definitions.

(defun bc32-step0-p (n x1)
  (equal
   x1
   (bc32-bv32-sub
    n
    (bc32-bv32-and
     (bc32-bv32-shiftr n 1)
     1431655765))))

(defun bc32-step1-p (x1 x2)
  (equal
   x2
   (bc32-bv32-add
    (bc32-bv32-and x1 858993459)
    (bc32-bv32-and
     (bc32-bv32-shiftr x1 2)
     858993459))))

(defun bc32-step2-p (x2 x3)
  (equal
   x3
   (bc32-bv32-and
    (bc32-bv32-add
     x2
     (bc32-bv32-shiftr x2 4))
    252645135)))

(defun bc32-step3-p (x3 x4)
  (equal
   x4
   (bc32-bv32-add
    x3
    (bc32-bv32-shiftr x3 8))))

(defun bc32-step4-p (x4 x5)
  (equal
   x5
   (bc32-bv32-add
    x4
    (bc32-bv32-shiftr x4 16))))

(defun
    ntp4vc-pearl-bitcount-bitcounting32-countqtvc-statement
    (n)
  (implies
   (bc32-bv32-p n)
   (let*
       ((x1
         (bc32-bv32-sub
          n
          (bc32-bv32-and
           (bc32-bv32-shiftr n 1)
           1431655765)))
        (x2
         (bc32-bv32-add
          (bc32-bv32-and x1 858993459)
          (bc32-bv32-and
           (bc32-bv32-shiftr x1 2)
           858993459)))
        (x3
         (bc32-bv32-and
          (bc32-bv32-add
           x2
           (bc32-bv32-shiftr x2 4))
          252645135))
        (x4
         (bc32-bv32-add
          x3
          (bc32-bv32-shiftr x3 8)))
        (x5
         (bc32-bv32-add
          x4
          (bc32-bv32-shiftr x4 16)))
        (masked-count
         (bc32-bv32-and x5 63)))
     (and
      (bc32-step0-p n x1)
      (bc32-step1-p x1 x2)
      (bc32-step2-p x2 x3)
      (bc32-step3-p x3 x4)
      (bc32-step4-p x4 x5)
      (implies
       (equal
        masked-count
        (bc32-numof-nth-closure n 0 32))
       (equal
        masked-count
        (bc32-count-logic n)))))))

(value-triple :itpeval-statement-checked)
:q
