;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_3_preserved_goal8:
;; preservation of the third strncmp loop invariant, concluding address
;; bounds after advancing the first current address by one, under the stated
;; bounded-string, byte, offset, and pointwise equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng8-address-base (address)
  (car address))

(defun sng8-address-offset (address)
  (cdr address))

(defun sng8-shift (address amount)
  (cons
   (sng8-address-base address)
   (+ (sng8-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, C integer conversions, linkedness, and
;; constancy symbols.

(defstub sng8-character-memory (address) t)
(defstub sng8-allocation (index) t)
(defstub sng8-region (base) t)
(defstub sng8-addr-le-op (left right) t)
(defstub sng8-l-strnlen (address count) t)
(defstub sng8-to-uint8 (value) t)
(defstub sng8-to-uint64 (value) t)
(defstub sng8-linked-op () t)
(defstub sng8-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng8-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (sng8-address-p address)
      (and
       (integerp
        (sng8-character-memory address))
       (implies
        (integerp count)
        (integerp
         (sng8-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (sng8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng8-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng8-to-uint8 value))
       (integerp
        (sng8-to-uint64 value)))))))

(defun sng8-addr-le-p (left right)
  (if (sng8-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sng8-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sng8-address-p left)
      (sng8-address-p right)
      (equal
       (sng8-address-base left)
       (sng8-address-base right)))
     (equal
      (sng8-addr-le-p left right)
      (<=
       (sng8-address-offset left)
       (sng8-address-offset right))))))

(defun sng8-linked-p ()
  (if (sng8-linked-op) t nil))

(defun sng8-sconst-p ()
  (if (sng8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng8-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned C integer conversions used by this VC and its strnlen recurrence.

(defun-sk sng8-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng8-is-uint8-p
       (sng8-to-uint8 value))
      (implies
       (sng8-is-uint8-p value)
       (equal
        (sng8-to-uint8 value)
        value))
      (equal
       (sng8-to-uint8
        (sng8-to-uint8 value))
       (sng8-to-uint8 value))))))

(defun-sk sng8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng8-is-uint64-p
       (sng8-to-uint64 value))
      (implies
       (sng8-is-uint64-p value)
       (equal
        (sng8-to-uint64 value)
        value))
      (equal
       (sng8-to-uint64
        (sng8-to-uint64 value))
       (sng8-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng8-address-base address))
    (<= 0
        (sng8-address-offset address))
    (<=
     (+ (sng8-address-offset address)
        length)
     (sng8-allocation
      (sng8-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk sng8-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng8-character-memory
       (sng8-shift address index))
      0)
     (< index count)
     (sng8-is-uint64-p index)
     (sng8-valid-rw-p
      (sng8-shift address 0)
      (+ 1 index)))))

(defun-sk sng8-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (sng8-is-sint8-p
       (sng8-character-memory
        (sng8-shift address position)))))))

(defun sng8-valid-bounded-string-p
    (address count)
  (or
   (sng8-valid-rw-p
    (sng8-shift address 0)
    (+ 1 count))
   (and
    (sng8-bounded-zero-witness-p
     address count)
    (sng8-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk sng8-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (sng8-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (sng8-character-memory
             (sng8-shift address 0))
            0))
          (equal
           (sng8-l-strnlen address count)
           0)
        (equal
         (sng8-to-uint64
          (+ 1
             (sng8-l-strnlen
              (sng8-shift address 1)
              (sng8-to-uint64
               (- count 1)))))
         (sng8-l-strnlen address count)))
      (sng8-is-uint64-p
       (sng8-l-strnlen address count))))))

;; The two source pointwise hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk sng8-offset-prefix-equal-before-p
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
        (sng8-character-memory
         (sng8-shift left position))
        (sng8-character-memory
         (sng8-shift right position))))))))

(defun-sk sng8-uint8-equality-reflects-p
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
         (sng8-to-uint8
          (sng8-character-memory
           (sng8-shift left position)))
         (sng8-to-uint8
          (sng8-character-memory
           (sng8-shift right position))))
        (equal
         (sng8-character-memory
          (sng8-shift left position))
         (sng8-character-memory
          (sng8-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-loop-inv-3-preserved-goal8-statement ()
  (forall
   (a1 a3 a2 a i)
   (implies
    (and
     (sng8-address-p a1)
     (sng8-address-p a3)
     (sng8-address-p a2)
     (sng8-address-p a)
     (integerp i)
     (sng8-function-types-p)
     (sng8-address-order-law-p)
     (sng8-to-uint8-laws-p)
     (sng8-to-uint64-laws-p)
     (sng8-strnlen-laws-p))
    (let*
        ((x
          (sng8-character-memory a1))
         (x1
          (sng8-to-uint8 x))
         (x2
          (sng8-character-memory a3))
         (x3
          (sng8-address-offset a1))
         (x4
          (sng8-address-offset a2))
         (x5
          (sng8-address-offset a))
         (x6
          (sng8-address-offset a3))
         (x7
          (- x6 x4))
         (x8
          (sng8-character-memory
           (sng8-shift a2 x7)))
         (x9
          (sng8-character-memory
           (sng8-shift a x7)))
         (x10
          (- (+ i x3) x5))
         (x11
          (sng8-l-strnlen a x10))
         (x12
          (sng8-l-strnlen a2 x10))
         (a4
          (sng8-shift a x11))
         (a5
          (sng8-shift a1 1)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x1 0))
        (equal
         (sng8-to-uint8 x2)
         x1)
        (equal
         (+ x3 x4)
         (+ x5 x6))
        (equal x8 x9)
        (equal
         (+ x5 x11)
         (+ x3
            (sng8-l-strnlen a1 i)))
        (equal
         (+ x4 x12)
         (+ x6
            (sng8-l-strnlen a3 i)))
        (<= 0 i)
        (<= x5 x3)
        (<=
         (sng8-region
          (sng8-address-base a))
         0)
        (<=
         (sng8-region
          (sng8-address-base a2))
         0)
        (sng8-linked-p)
        (sng8-sconst-p)
        (sng8-is-uint64-p i)
        (sng8-addr-le-p a a1)
        (sng8-addr-le-p a2 a3)
        (sng8-is-sint8-p x)
        (sng8-is-sint8-p x2)
        (sng8-valid-bounded-string-p
         a1 i)
        (sng8-valid-bounded-string-p
         a3 i)
        (sng8-is-uint64-p x10)
        (sng8-is-sint8-p x9)
        (sng8-is-sint8-p x8)
        (sng8-valid-bounded-string-p
         a x10)
        (sng8-valid-bounded-string-p
         a2 x10)
        (sng8-addr-le-p a1 a4)
        (sng8-addr-le-p
         a3
         (sng8-shift a2 x12))
        (sng8-offset-prefix-equal-before-p
         a2 a x5 x3)
        (sng8-uint8-equality-reflects-p
         a2 a x12))
       (and
        (sng8-addr-le-p a a5)
        (sng8-addr-le-p a5 a4)))))))

(value-triple :itpeval-statement-checked)

:q
