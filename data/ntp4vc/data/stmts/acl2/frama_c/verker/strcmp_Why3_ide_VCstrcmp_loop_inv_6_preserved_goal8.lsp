;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_6_preserved_goal8:
;; preservation of the strcmp loop invariant relating valid strings, address
;; offsets, character equality, and the logical string-length recurrence.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg8-address-base (address)
  (car address))

(defun scg8-address-offset (address)
  (cdr address))

(defun scg8-shift (address amount)
  (cons
   (scg8-address-base address)
   (+ (scg8-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub scg8-character-memory (address) t)
(defstub scg8-allocation (index) t)
(defstub scg8-region (base) t)
(defstub scg8-addr-le-op (left right) t)
(defstub scg8-l-strlen (address) t)
(defstub scg8-l-strncmp (left right count) t)
(defstub scg8-to-uint8 (value) t)
(defstub scg8-to-sint8 (value) t)
(defstub scg8-to-uint64 (value) t)
(defstub scg8-to-sint64 (value) t)
(defstub scg8-linked-op () t)
(defstub scg8-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg8-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (scg8-address-p address)
      (and
       (integerp
        (scg8-character-memory address))
       (integerp
        (scg8-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg8-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg8-to-uint8 value))
       (integerp
        (scg8-to-sint8 value))
       (integerp
        (scg8-to-uint64 value))
       (integerp
        (scg8-to-sint64 value))))
     (implies
      (and
       (scg8-address-p left)
       (scg8-address-p right)
       (integerp count))
      (integerp
       (scg8-l-strncmp left right count))))))

(defun scg8-addr-le-p (left right)
  (if (scg8-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk scg8-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (scg8-address-p left)
      (scg8-address-p right)
      (equal
       (scg8-address-base left)
       (scg8-address-base right)))
     (equal
      (scg8-addr-le-p left right)
      (<=
       (scg8-address-offset left)
       (scg8-address-offset right))))))

(defun scg8-linked-p ()
  (if (scg8-linked-op) t nil))

(defun scg8-sconst-p ()
  (if (scg8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg8-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg8-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and the logical strlen recurrence.

(defun-sk scg8-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-uint8-p
       (scg8-to-uint8 value))
      (implies
       (scg8-is-uint8-p value)
       (equal
        (scg8-to-uint8 value)
        value))
      (equal
       (scg8-to-uint8
        (scg8-to-uint8 value))
       (scg8-to-uint8 value))))))

(defun-sk scg8-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-sint8-p
       (scg8-to-sint8 value))
      (implies
       (scg8-is-sint8-p value)
       (equal
        (scg8-to-sint8 value)
        value))
      (equal
       (scg8-to-sint8
        (scg8-to-sint8 value))
       (scg8-to-sint8 value))))))

(defun-sk scg8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-uint64-p
       (scg8-to-uint64 value))
      (implies
       (scg8-is-uint64-p value)
       (equal
        (scg8-to-uint64 value)
        value))
      (equal
       (scg8-to-uint64
        (scg8-to-uint64 value))
       (scg8-to-uint64 value))))))

(defun-sk scg8-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-sint64-p
       (scg8-to-sint64 value))
      (implies
       (scg8-is-sint64-p value)
       (equal
        (scg8-to-sint64 value)
        value))
      (equal
       (scg8-to-sint64
        (scg8-to-sint64 value))
       (scg8-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg8-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg8-to-sint8
        (scg8-to-uint8 value))
       (scg8-to-sint8 value))
      (equal
       (scg8-to-sint64
        (scg8-to-uint64 value))
       (scg8-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg8-address-base address))
    (<= 0
        (scg8-address-offset address))
    (<=
     (+ (scg8-address-offset address)
        length)
     (scg8-allocation
      (scg8-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg8-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg8-is-sint8-p
       (scg8-character-memory
        (scg8-shift address position)))))))

(defun-sk scg8-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg8-character-memory
       (scg8-shift address index))
      0)
     (scg8-is-uint64-p index)
     (scg8-valid-rw-p
      (scg8-shift address 0)
      (+ 1 index))
     (scg8-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg8-strlen-laws-p ()
  (forall (address)
    (implies
     (scg8-address-p address)
     (and
      (if
          (equal
           (scg8-character-memory
            (scg8-shift address 0))
           0)
          (equal
           (scg8-l-strlen address)
           0)
        (equal
         (scg8-to-uint64
          (+ 1
             (scg8-l-strlen
              (scg8-shift address 1))))
         (scg8-l-strlen address)))
      (scg8-is-uint64-p
       (scg8-l-strlen address))))))

;; Exact definitions of A_StrCmp.l_cmp and A_StrCmp.l_strcmp.

(defun scg8-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right) -1 1)))

(defun scg8-l-strcmp (left right)
  (scg8-l-strncmp
   left
   right
   (scg8-l-strlen left)))

;; Universal closure of A_StrCmp.fix_l_strncmp_1'.

(defun-sk scg8-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (scg8-address-p left)
      (scg8-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (scg8-l-strncmp left right count)
          0)
       (if
           (equal
            (scg8-character-memory
             (scg8-shift right 0))
            (scg8-character-memory
             (scg8-shift left 0)))
           (equal
            (scg8-l-strncmp
             (scg8-shift left 1)
             (scg8-shift right 1)
             (- count 1))
            (scg8-l-strncmp left right count))
         (equal
          (scg8-l-cmp
           (scg8-to-uint8
            (scg8-character-memory
             (scg8-shift left 0)))
           (scg8-to-uint8
            (scg8-character-memory
             (scg8-shift right 0))))
          (scg8-l-strncmp left right count)))))))

;; The source equality of universally quantified prefix properties is kept as
;; a biconditional between predicates quantified over every mathematical
;; integer.

(defun-sk scg8-uint8-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg8-to-uint8
         (scg8-character-memory
          (scg8-shift left position)))
        (scg8-to-uint8
         (scg8-character-memory
          (scg8-shift right position)))))))))

(defun-sk scg8-raw-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg8-character-memory
         (scg8-shift left position))
        (scg8-character-memory
         (scg8-shift right position))))))))

;; The final loop hypothesis retains its universal quantifier and strict
;; offset bound over all mathematical integers.

(defun-sk scg8-raw-prefix-equal-before-offset-p
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
        (scg8-character-memory
         (scg8-shift left position))
        (scg8-character-memory
         (scg8-shift right position))))))))

(defun-sk
    ntp4vc-strcmp-loop-inv-6-preserved-goal8-statement ()
  (forall
   (a a2 a3 a1)
   (implies
    (and
     (scg8-address-p a)
     (scg8-address-p a2)
     (scg8-address-p a3)
     (scg8-address-p a1)
     (scg8-function-types-p)
     (scg8-address-order-law-p)
     (scg8-to-uint8-laws-p)
     (scg8-to-sint8-laws-p)
     (scg8-to-uint64-laws-p)
     (scg8-to-sint64-laws-p)
     (scg8-signed-unsigned-projection-laws-p)
     (scg8-strlen-laws-p)
     (scg8-strncmp-law-p))
    (let*
        ((x
          (scg8-character-memory a))
         (x1
          (scg8-to-uint8 x))
         (x2
          (scg8-character-memory a2))
         (x3
          (scg8-address-offset a2))
         (x4
          (scg8-address-offset a3))
         (x5
          (scg8-l-strlen a3))
         (x6
          (+ x4 x5))
         (x7
          (- x3 x4))
         (x8
          (scg8-character-memory
           (scg8-shift a3 x7)))
         (x9
          (scg8-character-memory
           (scg8-shift a1 x7))))
      (implies
       (and
        (not (equal x1 0))
        (equal
         (scg8-to-uint8 x2)
         x1)
        (equal
         (scg8-l-strcmp a3 a1)
         (scg8-l-strcmp a2 a))
        (equal
         (+ (scg8-address-offset a1)
            x3)
         (+ (scg8-address-offset a)
            x4))
        (equal
         x6
         (+ x3
            (scg8-l-strlen a2)))
        (equal x8 x9)
        (iff
         (scg8-uint8-prefix-equal-through-p
          a3 a1 x5)
         (scg8-raw-prefix-equal-through-p
          a3 a1 x5))
        (<=
         (scg8-region
          (scg8-address-base a1))
         0)
        (<=
         (scg8-region
          (scg8-address-base a3))
         0)
        (scg8-linked-p)
        (scg8-sconst-p)
        (scg8-addr-le-p a1 a)
        (scg8-addr-le-p a3 a2)
        (scg8-is-sint8-p x)
        (scg8-is-sint8-p x2)
        (scg8-valid-string-p a)
        (scg8-valid-string-p a1)
        (scg8-valid-string-p a2)
        (scg8-valid-string-p a3)
        (scg8-addr-le-p
         a
         (scg8-shift
          a1
          (scg8-l-strlen a1)))
        (scg8-addr-le-p
         a2
         (scg8-shift a3 x5))
        (scg8-is-sint8-p x9)
        (scg8-is-sint8-p x8)
        (scg8-raw-prefix-equal-before-offset-p
         a3 a1 x4 x3))
       (equal
        (+ 1
           x3
           (scg8-l-strlen
            (scg8-shift a2 1)))
        x6))))))

(value-triple :itpeval-statement-checked)

:q
