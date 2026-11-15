;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_6_preserved_goal12:
;; preservation of the sixth strncmp loop invariant, concluding the logical
;; strnlen recurrence after advancing the second current address by one, under
;; the stated bounded-string, byte, offset, and pointwise equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng12-address-base (address)
  (car address))

(defun sng12-address-offset (address)
  (cdr address))

(defun sng12-shift (address amount)
  (cons
   (sng12-address-base address)
   (+ (sng12-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, C integer conversions, linkedness, and
;; constancy symbols.

(defstub sng12-character-memory (address) t)
(defstub sng12-allocation (index) t)
(defstub sng12-region (base) t)
(defstub sng12-addr-le-op (left right) t)
(defstub sng12-l-strnlen (address count) t)
(defstub sng12-to-uint8 (value) t)
(defstub sng12-to-sint8 (value) t)
(defstub sng12-to-uint64 (value) t)
(defstub sng12-to-sint64 (value) t)
(defstub sng12-linked-op () t)
(defstub sng12-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng12-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (sng12-address-p address)
      (and
       (integerp
        (sng12-character-memory address))
       (implies
        (integerp count)
        (integerp
         (sng12-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (sng12-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng12-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng12-to-uint8 value))
       (integerp
        (sng12-to-sint8 value))
       (integerp
        (sng12-to-uint64 value))
       (integerp
        (sng12-to-sint64 value)))))))

(defun sng12-addr-le-p (left right)
  (if (sng12-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sng12-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sng12-address-p left)
      (sng12-address-p right)
      (equal
       (sng12-address-base left)
       (sng12-address-base right)))
     (equal
      (sng12-addr-le-p left right)
      (<=
       (sng12-address-offset left)
       (sng12-address-offset right))))))

(defun sng12-linked-p ()
  (if (sng12-linked-op) t nil))

(defun sng12-sconst-p ()
  (if (sng12-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng12-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng12-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sng12-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng12-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its strnlen recurrence.

(defun-sk sng12-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng12-is-uint8-p
       (sng12-to-uint8 value))
      (implies
       (sng12-is-uint8-p value)
       (equal
        (sng12-to-uint8 value)
        value))
      (equal
       (sng12-to-uint8
        (sng12-to-uint8 value))
       (sng12-to-uint8 value))))))

(defun-sk sng12-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng12-is-sint8-p
       (sng12-to-sint8 value))
      (implies
       (sng12-is-sint8-p value)
       (equal
        (sng12-to-sint8 value)
        value))
      (equal
       (sng12-to-sint8
        (sng12-to-sint8 value))
       (sng12-to-sint8 value))))))

(defun-sk sng12-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng12-is-uint64-p
       (sng12-to-uint64 value))
      (implies
       (sng12-is-uint64-p value)
       (equal
        (sng12-to-uint64 value)
        value))
      (equal
       (sng12-to-uint64
        (sng12-to-uint64 value))
       (sng12-to-uint64 value))))))

(defun-sk sng12-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng12-is-sint64-p
       (sng12-to-sint64 value))
      (implies
       (sng12-is-sint64-p value)
       (equal
        (sng12-to-sint64 value)
        value))
      (equal
       (sng12-to-sint64
        (sng12-to-sint64 value))
       (sng12-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk sng12-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sng12-to-sint8
        (sng12-to-uint8 value))
       (sng12-to-sint8 value))
      (equal
       (sng12-to-sint64
        (sng12-to-uint64 value))
       (sng12-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng12-address-base address))
    (<= 0
        (sng12-address-offset address))
    (<=
     (+ (sng12-address-offset address)
        length)
     (sng12-allocation
      (sng12-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk sng12-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng12-character-memory
       (sng12-shift address index))
      0)
     (< index count)
     (sng12-is-uint64-p index)
     (sng12-valid-rw-p
      (sng12-shift address 0)
      (+ 1 index)))))

(defun-sk sng12-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (sng12-is-sint8-p
       (sng12-character-memory
        (sng12-shift address position)))))))

(defun sng12-valid-bounded-string-p
    (address count)
  (or
   (sng12-valid-rw-p
    (sng12-shift address 0)
    (+ 1 count))
   (and
    (sng12-bounded-zero-witness-p
     address count)
    (sng12-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk sng12-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (sng12-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (sng12-character-memory
             (sng12-shift address 0))
            0))
          (equal
           (sng12-l-strnlen address count)
           0)
        (equal
         (sng12-to-uint64
          (+ 1
             (sng12-l-strnlen
              (sng12-shift address 1)
              (sng12-to-uint64
               (- count 1)))))
         (sng12-l-strnlen address count)))
      (sng12-is-uint64-p
       (sng12-l-strnlen address count))))))

;; The two source pointwise hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk sng12-offset-prefix-equal-before-p
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
        (sng12-character-memory
         (sng12-shift left position))
        (sng12-character-memory
         (sng12-shift right position))))))))

(defun-sk sng12-uint8-equality-reflects-p
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
         (sng12-to-uint8
          (sng12-character-memory
           (sng12-shift left position)))
         (sng12-to-uint8
          (sng12-character-memory
           (sng12-shift right position))))
        (equal
         (sng12-character-memory
          (sng12-shift left position))
         (sng12-character-memory
          (sng12-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-loop-inv-6-preserved-goal12-statement ()
  (forall
   (a2 a3 a1 a i)
   (implies
    (and
     (sng12-address-p a2)
     (sng12-address-p a3)
     (sng12-address-p a1)
     (sng12-address-p a)
     (integerp i)
     (sng12-function-types-p)
     (sng12-address-order-law-p)
     (sng12-to-uint8-laws-p)
     (sng12-to-sint8-laws-p)
     (sng12-to-uint64-laws-p)
     (sng12-to-sint64-laws-p)
     (sng12-signed-unsigned-projection-laws-p)
     (sng12-strnlen-laws-p))
    (let*
        ((x
          (sng12-character-memory a2))
         (x1
          (sng12-to-uint8 x))
         (x2
          (sng12-character-memory a3))
         (x3
          (sng12-address-offset a1))
         (x4
          (sng12-address-offset a3))
         (x5
          (sng12-address-offset a))
         (x6
          (sng12-address-offset a2))
         (x7
          (- x4 x5))
         (x8
          (sng12-character-memory
           (sng12-shift a1 x7)))
         (x9
          (sng12-character-memory
           (sng12-shift a x7)))
         (x10
          (- (+ i x6) x3))
         (x11
          (sng12-l-strnlen a x10))
         (x12
          (+ x5 x11))
         (x13
          (sng12-l-strnlen a1 x10)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x1 0))
        (equal
         (sng12-to-uint8 x2)
         x1)
        (equal
         (+ x3 x4)
         (+ x5 x6))
        (equal x8 x9)
        (equal
         x12
         (+ x4
            (sng12-l-strnlen a3 i)))
        (equal
         (+ x3 x13)
         (+ x6
            (sng12-l-strnlen a2 i)))
        (<= 0 i)
        (<= x3 x6)
        (<=
         (sng12-region
          (sng12-address-base a))
         0)
        (<=
         (sng12-region
          (sng12-address-base a1))
         0)
        (sng12-linked-p)
        (sng12-sconst-p)
        (sng12-is-uint64-p i)
        (sng12-addr-le-p a a3)
        (sng12-addr-le-p a1 a2)
        (sng12-is-sint8-p x)
        (sng12-is-sint8-p x2)
        (sng12-valid-bounded-string-p
         a2 i)
        (sng12-valid-bounded-string-p
         a3 i)
        (sng12-is-uint64-p x10)
        (sng12-is-sint8-p x9)
        (sng12-is-sint8-p x8)
        (sng12-valid-bounded-string-p
         a x10)
        (sng12-valid-bounded-string-p
         a1 x10)
        (sng12-addr-le-p
         a2
         (sng12-shift a1 x13))
        (sng12-addr-le-p
         a3
         (sng12-shift a x11))
        (sng12-offset-prefix-equal-before-p
         a1 a x3 x6)
        (sng12-uint8-equality-reflects-p
         a1 a x11))
       (equal
        x12
        (+ 1
           x4
           (sng12-l-strnlen
            (sng12-shift a3 1)
            (sng12-to-uint64
             (- i 1))))))))))

(value-triple :itpeval-statement-checked)

:q
