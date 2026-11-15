;; Statement-only formalization of the NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_getbitsqtvc: the verification condition for
;; extracting a nonempty bit window from a multiprecision integer, including
;; one- and two-limb cases and the resulting prefix-value equations. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defconst *gbitsq-radix* 18446744073709551616)

;; Canonical integers in [0, 2^w) represent source bitvectors exactly.

(defun gbitsq-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun gbitsq-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value *gbitsq-radix*)))

(defun gbitsq-sint32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun gbitsq-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun gbitsq-uint64-in-bounds-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (<= value 18446744073709551615)))

;; Pointers and zones remain arbitrary inhabited source carriers.  These
;; conservative interfaces expose exactly the observations used by the VC.

(defstub gbitsq-pointer-p (pointer) t)
(defstub gbitsq-zone-p (zone) t)
(defstub gbitsq-data (pointer) t)
(defstub gbitsq-offset (pointer) t)
(defstub gbitsq-minimum (pointer) t)
(defstub gbitsq-maximum (pointer) t)
(defstub gbitsq-writable (pointer) t)
(defstub gbitsq-zone (pointer) t)

(defun gbitsq-bv64-list-p (values)
  (if (consp values)
      (and
       (gbitsq-bv64-p (car values))
       (gbitsq-bv64-list-p (cdr values)))
    (equal values nil)))

(defun-sk gbitsq-pointer-domain-nonempty-p ()
  (exists (pointer)
    (gbitsq-pointer-p pointer)))

(defun-sk gbitsq-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (gbitsq-pointer-p pointer)
     (and
      (gbitsq-bv64-list-p
       (gbitsq-data pointer))
      (integerp (gbitsq-offset pointer))
      (integerp (gbitsq-minimum pointer))
      (integerp (gbitsq-maximum pointer))
      (booleanp (gbitsq-writable pointer))
      (gbitsq-zone-p
       (gbitsq-zone pointer))))))

(defun gbitsq-interface-p ()
  (and
   (gbitsq-pointer-domain-nonempty-p)
   (gbitsq-pointer-selectors-typed-p)))

;; Int.toNat sends every nonpositive integer to zero.  The source's total list
;; access uses the zero limb outside the represented data.

(defun gbitsq-int-to-nat (value)
  (if (and
       (integerp value)
       (< 0 value))
      value
    0))

(defun gbitsq-pelt (pointer index)
  (let ((natural-index
         (gbitsq-int-to-nat index)))
    (if (< natural-index
           (len (gbitsq-data pointer)))
        (nth natural-index
             (gbitsq-data pointer))
      0)))

(defun gbitsq-plength (pointer)
  (len (gbitsq-data pointer)))

;; This is mach.c.C.valid after expanding the signed-32 size bound and pointer
;; interval conditions.

(defun gbitsq-valid-p (pointer size)
  (and
   (gbitsq-pointer-p pointer)
   (gbitsq-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (gbitsq-minimum pointer))
   (<= (gbitsq-minimum pointer)
       (gbitsq-offset pointer))
   (<= (+ (gbitsq-offset pointer) size)
       (gbitsq-maximum pointer))
   (<= (gbitsq-maximum pointer)
       (gbitsq-plength pointer))))

;; Why3 machine signed division and remainder truncate toward zero.

(defun gbitsq-tdiv (left right)
  (if (or
       (not (integerp left))
       (not (integerp right))
       (equal right 0))
      0
    (let ((quotient
           (floor (abs left)
                  (abs right))))
      (if (< (* left right) 0)
          (- quotient)
        quotient))))

(defun gbitsq-tmod (left right)
  (- left
     (* right
        (gbitsq-tdiv left right))))

(defun gbitsq-ipow (base exponent)
  (expt base (nfix exponent)))

;; Little-endian radix-2^64 value of a pointer prefix.

(defun gbitsq-value-count (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (gbitsq-pelt pointer index)
     (*
      *gbitsq-radix*
      (gbitsq-value-count
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun gbitsq-value (pointer size)
  (gbitsq-value-count
   pointer
   (gbitsq-offset pointer)
   size))

(defun gbitsq-valueb (pointer nbits)
  (if (< nbits 0)
      0
    (let* ((index (floor nbits 64))
           (remaining
            (- nbits (* 64 index))))
      (+
       (gbitsq-value pointer index)
       (*
        (gbitsq-ipow *gbitsq-radix* index)
        (mod
         (gbitsq-pelt
          pointer
          (+ (gbitsq-offset pointer)
             index))
         (gbitsq-ipow 2 remaining)))))))

;; Equality of the source integer-indexed pelts maps.

(defun-sk gbitsq-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (gbitsq-pelt left index)
      (gbitsq-pelt right index)))))

(defun gbitsq-shifted-pointer-p
    (shifted original shift)
  (and
   (equal
    (gbitsq-offset shifted)
    (+ (gbitsq-offset original)
       shift))
   (equal
    (gbitsq-plength shifted)
    (gbitsq-plength original))
   (gbitsq-same-pelts-p
    shifted original)
   (equal
    (gbitsq-data shifted)
    (gbitsq-data original))
   (equal
    (gbitsq-minimum shifted)
    (gbitsq-minimum original))
   (equal
    (gbitsq-maximum shifted)
    (gbitsq-maximum original))
   (equal
    (gbitsq-zone shifted)
    (gbitsq-zone original))
   (equal
    (gbitsq-writable shifted)
    (gbitsq-writable original))))

;; The four getbits postconditions are shared by all result continuations.

(defun gbitsq-result-postcondition-p
    (pointer pn bi nbits result)
  (and
   (implies
    (<= (gbitsq-sint32 nbits)
        (gbitsq-sint32 bi))
    (equal
     (gbitsq-valueb
      pointer
      (gbitsq-sint32 bi))
     (+
      (gbitsq-valueb
       pointer
       (- (gbitsq-sint32 bi)
          (gbitsq-sint32 nbits)))
      (*
       (gbitsq-ipow
        2
        (- (gbitsq-sint32 bi)
           (gbitsq-sint32 nbits)))
       result))))
   (implies
    (< (gbitsq-sint32 bi)
       (gbitsq-sint32 nbits))
    (equal
     (gbitsq-valueb
      pointer
      (gbitsq-sint32 bi))
     result))
   (<= 0 result)
   (< result
      (gbitsq-ipow
       2
       (gbitsq-sint32 nbits)))
   (implies
    (<= (gbitsq-sint32 nbits)
        (gbitsq-sint32 bi))
    (equal
     result
     (mod
      (floor
       (gbitsq-value
        pointer
        (gbitsq-sint32 pn))
       (gbitsq-ipow
        2
        (- (gbitsq-sint32 bi)
           (gbitsq-sint32 nbits))))
      (gbitsq-ipow
       2
       (gbitsq-sint32 nbits)))))))

(defun gbitsq-result-body-p
    (pointer pn bi nbits dividend divisor result)
  (implies
   (equal
    result
    (gbitsq-tmod dividend divisor))
   (gbitsq-result-postcondition-p
    pointer pn bi nbits result)))

(defun-sk gbitsq-all-results-p
    (pointer pn bi nbits dividend divisor)
  (forall (result)
    (implies
     (gbitsq-bv64-p result)
     (gbitsq-result-body-p
      pointer pn bi nbits
      dividend divisor result))))

(defun gbitsq-reduced-result-p
    (pointer pn bi nbits dividend divisor)
  (and
   (not (equal divisor 0))
   (gbitsq-uint64-in-bounds-p
    (gbitsq-tmod dividend divisor))
   (gbitsq-all-results-p
    pointer pn bi nbits
    dividend divisor)))

;; The bi < nbits branch reads and masks the first limb.

(defun gbitsq-small-o2-body-p
    (pointer pn bi nbits o1 o2)
  (implies
   (equal
    o2
    (*
     (gbitsq-ipow 2 o1)
     1))
   (and
    (<= (gbitsq-minimum pointer)
        (gbitsq-offset pointer))
    (< (gbitsq-offset pointer)
       (gbitsq-maximum pointer))
    (gbitsq-reduced-result-p
     pointer pn bi nbits
     (gbitsq-pelt
      pointer
      (gbitsq-offset pointer))
     o2))))

(defun-sk gbitsq-all-small-o2-p
    (pointer pn bi nbits o1)
  (forall (o2)
    (implies
     (gbitsq-bv64-p o2)
     (gbitsq-small-o2-body-p
      pointer pn bi nbits o1 o2))))

(defun gbitsq-small-o1-body-p
    (pointer pn bi nbits o1)
  (implies
   (equal
    o1
    (gbitsq-sint32 bi))
   (and
    (and
     (<= 0 o1)
     (< o1 64))
    (<=
     (*
      (gbitsq-ipow 2 o1)
      1)
     18446744073709551615)
    (gbitsq-all-small-o2-p
     pointer pn bi nbits o1))))

(defun-sk gbitsq-all-small-o1-p
    (pointer pn bi nbits)
  (forall (o1)
    (implies
     (gbitsq-bv64-p o1)
     (gbitsq-small-o1-body-p
      pointer pn bi nbits o1))))

(defun gbitsq-small-branch-p
    (pointer pn bi nbits)
  (and
   (<= 0 (gbitsq-sint32 bi))
   (gbitsq-all-small-o1-p
    pointer pn bi nbits)))

;; The no-second-limb branch masks the shifted first limb directly.

(defun gbitsq-one-limb-o8-body-p
    (pointer pn bi nbits shifted o7 o8)
  (implies
   (equal
    o8
    (*
     (gbitsq-ipow 2 o7)
     1))
   (gbitsq-reduced-result-p
    pointer pn bi nbits shifted o8)))

(defun-sk gbitsq-all-one-limb-o8-p
    (pointer pn bi nbits shifted o7)
  (forall (o8)
    (implies
     (gbitsq-bv64-p o8)
     (gbitsq-one-limb-o8-body-p
      pointer pn bi nbits shifted o7 o8))))

(defun gbitsq-one-limb-o7-body-p
    (pointer pn bi nbits shifted o7)
  (implies
   (equal
    o7
    (gbitsq-sint32 nbits))
   (and
    (and
     (<= 0 o7)
     (< o7 64))
    (<=
     (*
      (gbitsq-ipow 2 o7)
      1)
     18446744073709551615)
    (gbitsq-all-one-limb-o8-p
     pointer pn bi nbits shifted o7))))

(defun-sk gbitsq-all-one-limb-o7-p
    (pointer pn bi nbits shifted)
  (forall (o7)
    (implies
     (gbitsq-bv64-p o7)
     (gbitsq-one-limb-o7-body-p
      pointer pn bi nbits shifted o7))))

(defun gbitsq-one-limb-branch-p
    (pointer pn bi nbits shifted)
  (and
   (<= 0 (gbitsq-sint32 nbits))
   (gbitsq-all-one-limb-o7-p
    pointer pn bi nbits shifted)))

;; The two-limb branch combines the shifted current limb with the shifted next
;; limb, then masks the sum to nbits.

(defun gbitsq-two-limb-o12-body-p
    (pointer pn bi nbits combined o11 o12)
  (implies
   (equal
    o12
    (*
     (gbitsq-ipow 2 o11)
     1))
   (gbitsq-reduced-result-p
    pointer pn bi nbits combined o12)))

(defun-sk gbitsq-all-two-limb-o12-p
    (pointer pn bi nbits combined o11)
  (forall (o12)
    (implies
     (gbitsq-bv64-p o12)
     (gbitsq-two-limb-o12-body-p
      pointer pn bi nbits
      combined o11 o12))))

(defun gbitsq-two-limb-o11-body-p
    (pointer pn bi nbits combined o11)
  (implies
   (equal
    o11
    (gbitsq-sint32 nbits))
   (and
    (and
     (<= 0 o11)
     (< o11 64))
    (<=
     (*
      (gbitsq-ipow 2 o11)
      1)
     18446744073709551615)
    (gbitsq-all-two-limb-o12-p
     pointer pn bi nbits
     combined o11))))

(defun-sk gbitsq-all-two-limb-o11-p
    (pointer pn bi nbits combined)
  (forall (o11)
    (implies
     (gbitsq-bv64-p o11)
     (gbitsq-two-limb-o11-body-p
      pointer pn bi nbits combined o11))))

(defun gbitsq-two-limb-o10-body-p
    (pointer pn bi nbits shifted partial o10)
  (implies
   (equal o10 (+ shifted partial))
   (and
    (<= 0 (gbitsq-sint32 nbits))
    (gbitsq-all-two-limb-o11-p
     pointer pn bi nbits o10))))

(defun-sk gbitsq-all-two-limb-o10-p
    (pointer pn bi nbits shifted partial)
  (forall (o10)
    (implies
     (gbitsq-bv64-p o10)
     (gbitsq-two-limb-o10-body-p
      pointer pn bi nbits
      shifted partial o10))))

(defun gbitsq-p-double-prime-body-p
    (pointer pn bi nbits quotient shifted partial
     o9 p-double-prime)
  (declare (ignore quotient))
  (implies
   (gbitsq-shifted-pointer-p
    p-double-prime
    pointer
    (gbitsq-sint32 o9))
   (and
    (not (equal *gbitsq-radix* 0))
    (gbitsq-uint64-in-bounds-p
     (+ shifted partial))
    (gbitsq-all-two-limb-o10-p
     pointer pn bi nbits
     shifted partial))))

(defun-sk gbitsq-all-p-double-prime-p
    (pointer pn bi nbits quotient shifted partial o9)
  (forall (p-double-prime)
    (implies
     (gbitsq-pointer-p p-double-prime)
     (gbitsq-p-double-prime-body-p
      pointer pn bi nbits quotient
      shifted partial o9 p-double-prime))))

(defun gbitsq-two-limb-o9-body-p
    (pointer pn bi nbits quotient shifted partial o9)
  (implies
   (equal
    (gbitsq-sint32 o9)
    (+ (gbitsq-sint32 quotient) 2))
   (and
    (<=
     (gbitsq-minimum pointer)
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o9)))
    (<=
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o9))
     (gbitsq-maximum pointer))
    (gbitsq-all-p-double-prime-p
     pointer pn bi nbits quotient
     shifted partial o9))))

(defun-sk gbitsq-all-two-limb-o9-p
    (pointer pn bi nbits quotient shifted partial)
  (forall (o9)
    (implies
     (gbitsq-bv32-p o9)
     (gbitsq-two-limb-o9-body-p
      pointer pn bi nbits quotient
      shifted partial o9))))

(defun gbitsq-partial-body-p
    (pointer pn bi nbits quotient
     shifted remaining o7 o8 partial)
  (declare (ignore remaining))
  (implies
   (and
    (equal
     partial
     (mod
      (*
       (gbitsq-pelt
        pointer
        (+ (gbitsq-offset pointer)
           (gbitsq-sint32 o7)))
       (gbitsq-ipow 2 o8))
      *gbitsq-radix*))
    (<=
     partial
     (- *gbitsq-radix*
        (gbitsq-ipow 2 o8))))
   (and
    (gbitsq-int32-in-bounds-p
     (+ (gbitsq-sint32 quotient) 2))
    (gbitsq-all-two-limb-o9-p
     pointer pn bi nbits quotient
     shifted partial))))

(defun-sk gbitsq-all-partials-p
    (pointer pn bi nbits quotient
     shifted remaining o7 o8)
  (forall (partial)
    (implies
     (gbitsq-bv64-p partial)
     (gbitsq-partial-body-p
      pointer pn bi nbits quotient
      shifted remaining o7 o8 partial))))

(defun gbitsq-two-limb-o8-body-p
    (pointer pn bi nbits quotient
     shifted remaining o7 o8)
  (implies
   (equal
    o8
    (gbitsq-sint32 remaining))
   (and
    (and
     (<= 0 o8)
     (< o8 64))
    (gbitsq-all-partials-p
     pointer pn bi nbits quotient
     shifted remaining o7 o8))))

(defun-sk gbitsq-all-two-limb-o8-p
    (pointer pn bi nbits quotient
     shifted remaining o7)
  (forall (o8)
    (implies
     (gbitsq-bv64-p o8)
     (gbitsq-two-limb-o8-body-p
      pointer pn bi nbits quotient
      shifted remaining o7 o8))))

(defun gbitsq-two-limb-o7-body-p
    (pointer pn bi nbits quotient
     shifted remaining o7)
  (implies
   (equal
    (gbitsq-sint32 o7)
    (+ (gbitsq-sint32 quotient) 1))
   (and
    (<=
     (gbitsq-minimum pointer)
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o7)))
    (<
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o7))
     (gbitsq-maximum pointer))
    (<= 0 (gbitsq-sint32 remaining))
    (gbitsq-all-two-limb-o8-p
     pointer pn bi nbits quotient
     shifted remaining o7))))

(defun-sk gbitsq-all-two-limb-o7-p
    (pointer pn bi nbits quotient
     shifted remaining)
  (forall (o7)
    (implies
     (gbitsq-bv32-p o7)
     (gbitsq-two-limb-o7-body-p
      pointer pn bi nbits quotient
      shifted remaining o7))))

(defun gbitsq-two-limb-branch-p
    (pointer pn bi nbits quotient
     shifted remaining)
  (and
   (gbitsq-int32-in-bounds-p
    (+ (gbitsq-sint32 quotient) 1))
   (gbitsq-all-two-limb-o7-p
    pointer pn bi nbits quotient
    shifted remaining)))

;; Preserve the branch on the number of requested bits already present in the
;; shifted first limb.

(defun gbitsq-remaining-body-p
    (pointer pn bi nbits quotient
     shifted remainder remaining)
  (implies
   (equal
    (gbitsq-sint32 remaining)
    (- 64 (gbitsq-sint32 remainder)))
   (if (< (gbitsq-sint32 remaining)
          (gbitsq-sint32 nbits))
       (gbitsq-two-limb-branch-p
        pointer pn bi nbits quotient
        shifted remaining)
     (gbitsq-one-limb-branch-p
      pointer pn bi nbits shifted))))

(defun-sk gbitsq-all-remaining-p
    (pointer pn bi nbits quotient
     shifted remainder)
  (forall (remaining)
    (implies
     (gbitsq-bv32-p remaining)
     (gbitsq-remaining-body-p
      pointer pn bi nbits quotient
      shifted remainder remaining))))

(defun gbitsq-shifted-body-p
    (pointer pn bi nbits quotient
     remainder o5 shifted)
  (implies
   (equal
    shifted
    (floor
     (gbitsq-pelt
      pointer
      (+ (gbitsq-offset pointer)
         (gbitsq-sint32 quotient)))
     (gbitsq-ipow 2 o5)))
   (and
    (not
     (equal
      (gbitsq-ipow
       2
       (gbitsq-sint32 remainder))
      0))
    (gbitsq-int32-in-bounds-p
     (- 64 (gbitsq-sint32 remainder)))
    (gbitsq-all-remaining-p
     pointer pn bi nbits quotient
     shifted remainder))))

(defun-sk gbitsq-all-shifted-p
    (pointer pn bi nbits quotient
     remainder o5)
  (forall (shifted)
    (implies
     (gbitsq-bv64-p shifted)
     (gbitsq-shifted-body-p
      pointer pn bi nbits quotient
      remainder o5 shifted))))

(defun gbitsq-o5-body-p
    (pointer pn bi nbits quotient
     remainder o5)
  (implies
   (equal
    o5
    (gbitsq-sint32 remainder))
   (and
    (and
     (<= 0 o5)
     (< o5 64))
    (gbitsq-all-shifted-p
     pointer pn bi nbits quotient
     remainder o5))))

(defun-sk gbitsq-all-o5-p
    (pointer pn bi nbits quotient remainder)
  (forall (o5)
    (implies
     (gbitsq-bv64-p o5)
     (gbitsq-o5-body-p
      pointer pn bi nbits quotient
      remainder o5))))

(defun gbitsq-p-prime-body-p
    (pointer pn bi nbits quotient
     remainder o4 p-prime)
  (implies
   (gbitsq-shifted-pointer-p
    p-prime
    pointer
    (gbitsq-sint32 o4))
   (and
    (<= 0 (gbitsq-sint32 remainder))
    (gbitsq-all-o5-p
     pointer pn bi nbits
     quotient remainder))))

(defun-sk gbitsq-all-p-prime-p
    (pointer pn bi nbits quotient
     remainder o4)
  (forall (p-prime)
    (implies
     (gbitsq-pointer-p p-prime)
     (gbitsq-p-prime-body-p
      pointer pn bi nbits quotient
      remainder o4 p-prime))))

(defun gbitsq-o4-body-p
    (pointer pn bi nbits quotient
     remainder o4)
  (implies
   (equal
    (gbitsq-sint32 o4)
    (+ (gbitsq-sint32 quotient) 1))
   (and
    (<=
     (gbitsq-minimum pointer)
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o4)))
    (<=
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 o4))
     (gbitsq-maximum pointer))
    (gbitsq-all-p-prime-p
     pointer pn bi nbits quotient
     remainder o4))))

(defun-sk gbitsq-all-o4-p
    (pointer pn bi nbits quotient remainder)
  (forall (o4)
    (implies
     (gbitsq-bv32-p o4)
     (gbitsq-o4-body-p
      pointer pn bi nbits quotient
      remainder o4))))

(defun gbitsq-remainder-body-p
    (pointer pn bi nbits quotient
     difference remainder)
  (implies
   (equal
    (gbitsq-sint32 remainder)
    (gbitsq-tmod
     (gbitsq-sint32 difference)
     64))
   (and
    (<=
     (gbitsq-minimum pointer)
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 quotient)))
    (<
     (+ (gbitsq-offset pointer)
        (gbitsq-sint32 quotient))
     (gbitsq-maximum pointer))
    (gbitsq-int32-in-bounds-p
     (+ (gbitsq-sint32 quotient) 1))
    (gbitsq-all-o4-p
     pointer pn bi nbits
     quotient remainder))))

(defun-sk gbitsq-all-remainders-p
    (pointer pn bi nbits quotient difference)
  (forall (remainder)
    (implies
     (gbitsq-bv32-p remainder)
     (gbitsq-remainder-body-p
      pointer pn bi nbits quotient
      difference remainder))))

(defun gbitsq-quotient-body-p
    (pointer pn bi nbits difference quotient)
  (implies
   (equal
    (gbitsq-sint32 quotient)
    (gbitsq-tdiv
     (gbitsq-sint32 difference)
     64))
   (and
    (not (equal 64 0))
    (gbitsq-int32-in-bounds-p
     (gbitsq-tmod
      (gbitsq-sint32 difference)
      64))
    (gbitsq-all-remainders-p
     pointer pn bi nbits
     quotient difference))))

(defun-sk gbitsq-all-quotients-p
    (pointer pn bi nbits difference)
  (forall (quotient)
    (implies
     (gbitsq-bv32-p quotient)
     (gbitsq-quotient-body-p
      pointer pn bi nbits
      difference quotient))))

(defun gbitsq-difference-body-p
    (pointer pn bi nbits difference)
  (implies
   (equal
    (gbitsq-sint32 difference)
    (- (gbitsq-sint32 bi)
       (gbitsq-sint32 nbits)))
   (and
    (not (equal 64 0))
    (gbitsq-int32-in-bounds-p
     (gbitsq-tdiv
      (gbitsq-sint32 difference)
      64))
    (gbitsq-all-quotients-p
     pointer pn bi nbits difference))))

(defun-sk gbitsq-all-differences-p
    (pointer pn bi nbits)
  (forall (difference)
    (implies
     (gbitsq-bv32-p difference)
     (gbitsq-difference-body-p
      pointer pn bi nbits difference))))

(defun gbitsq-large-branch-p
    (pointer pn bi nbits)
  (and
   (gbitsq-int32-in-bounds-p
    (- (gbitsq-sint32 bi)
       (gbitsq-sint32 nbits)))
   (gbitsq-all-differences-p
    pointer pn bi nbits)))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-getbitsqtvc-statement
    (nbits bi pn pointer)
  (implies
   (and
    (gbitsq-interface-p)
    (gbitsq-bv32-p nbits)
    (gbitsq-bv32-p bi)
    (gbitsq-bv32-p pn)
    (gbitsq-pointer-p pointer)
    (<= 1 (gbitsq-sint32 nbits))
    (< (gbitsq-sint32 nbits) 64)
    (<= 0 (gbitsq-sint32 bi))
    (<= 1 (gbitsq-sint32 pn))
    (gbitsq-valid-p
     pointer
     (gbitsq-sint32 pn))
    (<=
     (floor
      (+ (gbitsq-sint32 bi) 63)
      64)
     (gbitsq-sint32 pn)))
   (if (< (gbitsq-sint32 bi)
          (gbitsq-sint32 nbits))
       (gbitsq-small-branch-p
        pointer pn bi nbits)
     (gbitsq-large-branch-p
      pointer pn bi nbits))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
