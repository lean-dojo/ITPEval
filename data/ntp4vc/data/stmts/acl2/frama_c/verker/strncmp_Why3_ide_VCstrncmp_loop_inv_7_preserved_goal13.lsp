;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_7_preserved_goal13:
;; preservation of the seventh strncmp loop invariant, concluding the logical
;; strnlen recurrence after advancing the first current address by one, under
;; the stated bounded-string, byte, offset, and pointwise equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng13-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng13-address-base (address)
  (car address))

(defun sng13-address-offset (address)
  (cdr address))

(defun sng13-shift (address amount)
  (cons
   (sng13-address-base address)
   (+ (sng13-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, C integer conversions, linkedness, and
;; constancy symbols.

(defstub sng13-character-memory (address) t)
(defstub sng13-allocation (index) t)
(defstub sng13-region (base) t)
(defstub sng13-addr-le-op (left right) t)
(defstub sng13-l-strnlen (address count) t)
(defstub sng13-to-uint8 (value) t)
(defstub sng13-to-uint64 (value) t)
(defstub sng13-linked-op () t)
(defstub sng13-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng13-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (sng13-address-p address)
      (and
       (integerp
        (sng13-character-memory address))
       (implies
        (integerp count)
        (integerp
         (sng13-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (sng13-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng13-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng13-to-uint8 value))
       (integerp
        (sng13-to-uint64 value)))))))

(defun sng13-addr-le-p (left right)
  (if (sng13-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sng13-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sng13-address-p left)
      (sng13-address-p right)
      (equal
       (sng13-address-base left)
       (sng13-address-base right)))
     (equal
      (sng13-addr-le-p left right)
      (<=
       (sng13-address-offset left)
       (sng13-address-offset right))))))

(defun sng13-linked-p ()
  (if (sng13-linked-op) t nil))

(defun sng13-sconst-p ()
  (if (sng13-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng13-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng13-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng13-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned C integer conversions used by this VC and its strnlen recurrence.

(defun-sk sng13-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng13-is-uint8-p
       (sng13-to-uint8 value))
      (implies
       (sng13-is-uint8-p value)
       (equal
        (sng13-to-uint8 value)
        value))
      (equal
       (sng13-to-uint8
        (sng13-to-uint8 value))
       (sng13-to-uint8 value))))))

(defun-sk sng13-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng13-is-uint64-p
       (sng13-to-uint64 value))
      (implies
       (sng13-is-uint64-p value)
       (equal
        (sng13-to-uint64 value)
        value))
      (equal
       (sng13-to-uint64
        (sng13-to-uint64 value))
       (sng13-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng13-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng13-address-base address))
    (<= 0
        (sng13-address-offset address))
    (<=
     (+ (sng13-address-offset address)
        length)
     (sng13-allocation
      (sng13-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk sng13-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng13-character-memory
       (sng13-shift address index))
      0)
     (< index count)
     (sng13-is-uint64-p index)
     (sng13-valid-rw-p
      (sng13-shift address 0)
      (+ 1 index)))))

(defun-sk sng13-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (sng13-is-sint8-p
       (sng13-character-memory
        (sng13-shift address position)))))))

(defun sng13-valid-bounded-string-p
    (address count)
  (or
   (sng13-valid-rw-p
    (sng13-shift address 0)
    (+ 1 count))
   (and
    (sng13-bounded-zero-witness-p
     address count)
    (sng13-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk sng13-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (sng13-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (sng13-character-memory
             (sng13-shift address 0))
            0))
          (equal
           (sng13-l-strnlen address count)
           0)
        (equal
         (sng13-to-uint64
          (+ 1
             (sng13-l-strnlen
              (sng13-shift address 1)
              (sng13-to-uint64
               (- count 1)))))
         (sng13-l-strnlen address count)))
      (sng13-is-uint64-p
       (sng13-l-strnlen address count))))))

;; The two source pointwise hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk sng13-offset-prefix-equal-before-p
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
        (sng13-character-memory
         (sng13-shift left position))
        (sng13-character-memory
         (sng13-shift right position))))))))

(defun-sk sng13-uint8-equality-reflects-p
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
         (sng13-to-uint8
          (sng13-character-memory
           (sng13-shift left position)))
         (sng13-to-uint8
          (sng13-character-memory
           (sng13-shift right position))))
        (equal
         (sng13-character-memory
          (sng13-shift left position))
         (sng13-character-memory
          (sng13-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-loop-inv-7-preserved-goal13-statement ()
  (forall
   (a1 a3 a2 a i)
   (implies
    (and
     (sng13-address-p a1)
     (sng13-address-p a3)
     (sng13-address-p a2)
     (sng13-address-p a)
     (integerp i)
     (sng13-function-types-p)
     (sng13-address-order-law-p)
     (sng13-to-uint8-laws-p)
     (sng13-to-uint64-laws-p)
     (sng13-strnlen-laws-p))
    (let*
        ((x
          (sng13-character-memory a1))
         (x1
          (sng13-to-uint8 x))
         (x2
          (sng13-character-memory a3))
         (x3
          (sng13-address-offset a1))
         (x4
          (sng13-address-offset a2))
         (x5
          (sng13-address-offset a))
         (x6
          (sng13-address-offset a3))
         (x7
          (- x6 x4))
         (x8
          (sng13-character-memory
           (sng13-shift a2 x7)))
         (x9
          (sng13-character-memory
           (sng13-shift a x7)))
         (x10
          (- (+ i x3) x5))
         (x11
          (sng13-l-strnlen a x10))
         (x12
          (+ x5 x11))
         (x13
          (sng13-l-strnlen a2 x10)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x1 0))
        (equal
         (sng13-to-uint8 x2)
         x1)
        (equal
         (+ x3 x4)
         (+ x5 x6))
        (equal x8 x9)
        (equal
         x12
         (+ x3
            (sng13-l-strnlen a1 i)))
        (equal
         (+ x4 x13)
         (+ x6
            (sng13-l-strnlen a3 i)))
        (<= 0 i)
        (<= x5 x3)
        (<=
         (sng13-region
          (sng13-address-base a))
         0)
        (<=
         (sng13-region
          (sng13-address-base a2))
         0)
        (sng13-linked-p)
        (sng13-sconst-p)
        (sng13-is-uint64-p i)
        (sng13-addr-le-p a a1)
        (sng13-addr-le-p a2 a3)
        (sng13-is-sint8-p x)
        (sng13-is-sint8-p x2)
        (sng13-valid-bounded-string-p
         a1 i)
        (sng13-valid-bounded-string-p
         a3 i)
        (sng13-is-uint64-p x10)
        (sng13-is-sint8-p x9)
        (sng13-is-sint8-p x8)
        (sng13-valid-bounded-string-p
         a x10)
        (sng13-valid-bounded-string-p
         a2 x10)
        (sng13-addr-le-p
         a1
         (sng13-shift a x11))
        (sng13-addr-le-p
         a3
         (sng13-shift a2 x13))
        (sng13-offset-prefix-equal-before-p
         a2 a x5 x3)
        (sng13-uint8-equality-reflects-p
         a2 a x13))
       (equal
        x12
        (+ 1
           x3
           (sng13-l-strnlen
            (sng13-shift a1 1)
            (sng13-to-uint64
             (- i 1))))))))))

(value-triple :itpeval-statement-checked)

:q
