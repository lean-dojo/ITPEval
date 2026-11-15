;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_2_preserved_goal6:
;; preservation of the second strncmp loop invariant, concluding the address
;; bounds after advancing the second current address by one, under the stated
;; bounded-string, byte, offset, and pointwise equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng6-address-base (address)
  (car address))

(defun sng6-address-offset (address)
  (cdr address))

(defun sng6-shift (address amount)
  (cons
   (sng6-address-base address)
   (+ (sng6-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, C integer conversions, linkedness, and
;; constancy symbols.

(defstub sng6-character-memory (address) t)
(defstub sng6-allocation (index) t)
(defstub sng6-region (base) t)
(defstub sng6-addr-le-op (left right) t)
(defstub sng6-l-strnlen (address count) t)
(defstub sng6-to-uint8 (value) t)
(defstub sng6-to-uint64 (value) t)
(defstub sng6-linked-op () t)
(defstub sng6-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng6-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (sng6-address-p address)
      (and
       (integerp
        (sng6-character-memory address))
       (implies
        (integerp count)
        (integerp
         (sng6-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (sng6-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng6-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng6-to-uint8 value))
       (integerp
        (sng6-to-uint64 value)))))))

(defun sng6-addr-le-p (left right)
  (if (sng6-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sng6-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sng6-address-p left)
      (sng6-address-p right)
      (equal
       (sng6-address-base left)
       (sng6-address-base right)))
     (equal
      (sng6-addr-le-p left right)
      (<=
       (sng6-address-offset left)
       (sng6-address-offset right))))))

(defun sng6-linked-p ()
  (if (sng6-linked-op) t nil))

(defun sng6-sconst-p ()
  (if (sng6-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng6-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng6-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned C integer conversions used by this VC and its strnlen recurrence.

(defun-sk sng6-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng6-is-uint8-p
       (sng6-to-uint8 value))
      (implies
       (sng6-is-uint8-p value)
       (equal
        (sng6-to-uint8 value)
        value))
      (equal
       (sng6-to-uint8
        (sng6-to-uint8 value))
       (sng6-to-uint8 value))))))

(defun-sk sng6-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng6-is-uint64-p
       (sng6-to-uint64 value))
      (implies
       (sng6-is-uint64-p value)
       (equal
        (sng6-to-uint64 value)
        value))
      (equal
       (sng6-to-uint64
        (sng6-to-uint64 value))
       (sng6-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng6-address-base address))
    (<= 0
        (sng6-address-offset address))
    (<=
     (+ (sng6-address-offset address)
        length)
     (sng6-allocation
      (sng6-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk sng6-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng6-character-memory
       (sng6-shift address index))
      0)
     (< index count)
     (sng6-is-uint64-p index)
     (sng6-valid-rw-p
      (sng6-shift address 0)
      (+ 1 index)))))

(defun-sk sng6-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (sng6-is-sint8-p
       (sng6-character-memory
        (sng6-shift address position)))))))

(defun sng6-valid-bounded-string-p
    (address count)
  (or
   (sng6-valid-rw-p
    (sng6-shift address 0)
    (+ 1 count))
   (and
    (sng6-bounded-zero-witness-p
     address count)
    (sng6-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk sng6-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (sng6-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (sng6-character-memory
             (sng6-shift address 0))
            0))
          (equal
           (sng6-l-strnlen address count)
           0)
        (equal
         (sng6-to-uint64
          (+ 1
             (sng6-l-strnlen
              (sng6-shift address 1)
              (sng6-to-uint64
               (- count 1)))))
         (sng6-l-strnlen address count)))
      (sng6-is-uint64-p
       (sng6-l-strnlen address count))))))

;; The two source pointwise hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk sng6-offset-prefix-equal-before-p
    (left right left-offset right-offset)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< (+ position left-offset)
          right-offset)
       (equal
        (sng6-character-memory
         (sng6-shift left position))
        (sng6-character-memory
         (sng6-shift right position))))))))

(defun-sk sng6-uint8-equality-reflects-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (iff
        (equal
         (sng6-to-uint8
          (sng6-character-memory
           (sng6-shift left position)))
         (sng6-to-uint8
          (sng6-character-memory
           (sng6-shift right position))))
        (equal
         (sng6-character-memory
          (sng6-shift left position))
         (sng6-character-memory
          (sng6-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-loop-inv-2-preserved-goal6-statement ()
  (forall
   (a2 a3 a1 a i)
   (implies
    (and
     (sng6-address-p a2)
     (sng6-address-p a3)
     (sng6-address-p a1)
     (sng6-address-p a)
     (integerp i)
     (sng6-function-types-p)
     (sng6-address-order-law-p)
     (sng6-to-uint8-laws-p)
     (sng6-to-uint64-laws-p)
     (sng6-strnlen-laws-p))
    (let*
        ((x
          (sng6-character-memory a2))
         (x1
          (sng6-to-uint8 x))
         (x2
          (sng6-character-memory a3))
         (x3
          (sng6-address-offset a1))
         (x4
          (sng6-address-offset a3))
         (x5
          (sng6-address-offset a))
         (x6
          (sng6-address-offset a2))
         (x7
          (- x4 x5))
         (x8
          (sng6-character-memory
           (sng6-shift a1 x7)))
         (x9
          (sng6-character-memory
           (sng6-shift a x7)))
         (x10
          (- (+ i x6) x3))
         (x11
          (sng6-l-strnlen a x10))
         (x12
          (sng6-l-strnlen a1 x10))
         (a4
          (sng6-shift a x11))
         (a5
          (sng6-shift a3 1)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x1 0))
        (equal
         (sng6-to-uint8 x2)
         x1)
        (equal
         (+ x3 x4)
         (+ x5 x6))
        (equal x8 x9)
        (equal
         (+ x5 x11)
         (+ x4
            (sng6-l-strnlen a3 i)))
        (equal
         (+ x3 x12)
         (+ x6
            (sng6-l-strnlen a2 i)))
        (<= 0 i)
        (<= x3 x6)
        (<=
         (sng6-region
          (sng6-address-base a))
         0)
        (<=
         (sng6-region
          (sng6-address-base a1))
         0)
        (sng6-linked-p)
        (sng6-sconst-p)
        (sng6-is-uint64-p i)
        (sng6-addr-le-p a a3)
        (sng6-addr-le-p a1 a2)
        (sng6-is-sint8-p x)
        (sng6-is-sint8-p x2)
        (sng6-valid-bounded-string-p
         a2 i)
        (sng6-valid-bounded-string-p
         a3 i)
        (sng6-is-uint64-p x10)
        (sng6-is-sint8-p x9)
        (sng6-is-sint8-p x8)
        (sng6-valid-bounded-string-p
         a x10)
        (sng6-valid-bounded-string-p
         a1 x10)
        (sng6-addr-le-p
         a2
         (sng6-shift a1 x12))
        (sng6-addr-le-p a3 a4)
        (sng6-offset-prefix-equal-before-p
         a1 a x3 x6)
        (sng6-uint8-equality-reflects-p
         a1 a x11))
       (and
        (sng6-addr-le-p a a5)
        (sng6-addr-le-p a5 a4)))))))

(value-triple :itpeval-statement-checked)

:q
