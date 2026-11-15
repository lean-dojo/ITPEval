;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23:
;; the strncmp length-difference verification condition concluding a positive
;; comparison result from address, bounded-string, byte-comparison, and
;; universally quantified prefix-equality hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snld23-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snld23-address-base (address)
  (car address))

(defun snld23-address-offset (address)
  (cdr address))

(defun snld23-shift (address amount)
  (cons
   (snld23-address-base address)
   (+ (snld23-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen and strnlen, C integer conversions,
;; linkedness, and constancy symbols.

(defstub snld23-character-memory (address) t)
(defstub snld23-allocation (index) t)
(defstub snld23-region (base) t)
(defstub snld23-addr-le-op (left right) t)
(defstub snld23-l-strlen (address) t)
(defstub snld23-l-strnlen (address count) t)
(defstub snld23-to-uint8 (value) t)
(defstub snld23-to-uint64 (value) t)
(defstub snld23-linked-op () t)
(defstub snld23-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snld23-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snld23-address-p address)
      (and
       (integerp
        (snld23-character-memory address))
       (integerp
        (snld23-l-strlen address))
       (implies
        (integerp count)
        (integerp
         (snld23-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snld23-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snld23-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snld23-to-uint8 value))
       (integerp
        (snld23-to-uint64 value)))))))

(defun snld23-addr-le-p (left right)
  (if (snld23-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snld23-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snld23-address-p left)
      (snld23-address-p right)
      (equal
       (snld23-address-base left)
       (snld23-address-base right)))
     (equal
      (snld23-addr-le-p left right)
      (<=
       (snld23-address-offset left)
       (snld23-address-offset right))))))

(defun snld23-linked-p ()
  (if (snld23-linked-op) t nil))

(defun snld23-sconst-p ()
  (if (snld23-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snld23-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snld23-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snld23-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun snld23-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned C integer conversions used by this VC and its string recurrences.

(defun-sk snld23-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snld23-is-uint8-p
       (snld23-to-uint8 value))
      (implies
       (snld23-is-uint8-p value)
       (equal
        (snld23-to-uint8 value)
        value))
      (equal
       (snld23-to-uint8
        (snld23-to-uint8 value))
       (snld23-to-uint8 value))))))

(defun-sk snld23-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snld23-is-uint64-p
       (snld23-to-uint64 value))
      (implies
       (snld23-is-uint64-p value)
       (equal
        (snld23-to-uint64 value)
        value))
      (equal
       (snld23-to-uint64
        (snld23-to-uint64 value))
       (snld23-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snld23-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snld23-address-base address))
    (<= 0
        (snld23-address-offset address))
    (<=
     (+ (snld23-address-offset address)
        length)
     (snld23-allocation
      (snld23-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk snld23-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snld23-is-sint8-p
       (snld23-character-memory
        (snld23-shift address position)))))))

(defun-sk snld23-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snld23-character-memory
       (snld23-shift address index))
      0)
     (snld23-is-uint64-p index)
     (snld23-valid-rw-p
      (snld23-shift address 0)
      (+ 1 index))
     (snld23-string-chars-sint8-through-p
      address index))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk snld23-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snld23-character-memory
       (snld23-shift address index))
      0)
     (< index count)
     (snld23-is-uint64-p index)
     (snld23-valid-rw-p
      (snld23-shift address 0)
      (+ 1 index)))))

(defun-sk snld23-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snld23-is-sint8-p
       (snld23-character-memory
        (snld23-shift address position)))))))

(defun snld23-valid-bounded-string-p
    (address count)
  (or
   (snld23-valid-rw-p
    (snld23-shift address 0)
    (+ 1 count))
   (and
    (snld23-bounded-zero-witness-p
     address count)
    (snld23-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk snld23-strlen-laws-p ()
  (forall (address)
    (implies
     (snld23-address-p address)
     (and
      (if
          (equal
           (snld23-character-memory
            (snld23-shift address 0))
           0)
          (equal
           (snld23-l-strlen address)
           0)
        (equal
         (snld23-to-uint64
          (+ 1
             (snld23-l-strlen
              (snld23-shift address 1))))
         (snld23-l-strlen address)))
      (snld23-is-uint64-p
       (snld23-l-strlen address))))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snld23-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snld23-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snld23-character-memory
             (snld23-shift address 0))
            0))
          (equal
           (snld23-l-strnlen address count)
           0)
        (equal
         (snld23-to-uint64
          (+ 1
             (snld23-l-strnlen
              (snld23-shift address 1)
              (snld23-to-uint64
               (- count 1)))))
         (snld23-l-strnlen address count)))
      (snld23-is-uint64-p
       (snld23-l-strnlen address count))))))

;; The three source prefix hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk snld23-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (snld23-character-memory
         (snld23-shift left position))
        (snld23-character-memory
         (snld23-shift right position))))))))

(defun-sk snld23-offset-prefix-equal-before-p
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
        (snld23-character-memory
         (snld23-shift left position))
        (snld23-character-memory
         (snld23-shift right position))))))))

(defun-sk snld23-uint8-equality-reflects-p
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
         (snld23-to-uint8
          (snld23-character-memory
           (snld23-shift left position)))
         (snld23-to-uint8
          (snld23-character-memory
           (snld23-shift right position))))
        (equal
         (snld23-character-memory
          (snld23-shift left position))
         (snld23-character-memory
          (snld23-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-len-diff-post-2-goal23-statement ()
  (forall
   (a1 a2 a a3 i1 i2 i3 result)
   (implies
    (and
     (snld23-address-p a1)
     (snld23-address-p a2)
     (snld23-address-p a)
     (snld23-address-p a3)
     (integerp i1)
     (integerp i2)
     (integerp i3)
     (integerp result)
     (snld23-function-types-p)
     (snld23-address-order-law-p)
     (snld23-to-uint8-laws-p)
     (snld23-to-uint64-laws-p)
     (snld23-strlen-laws-p)
     (snld23-strnlen-laws-p))
    (let*
        ((x
          (snld23-address-offset a1))
         (x1
          (snld23-address-offset a2))
         (x2
          (snld23-address-offset a))
         (x3
          (snld23-address-offset a3))
         (x4
          (- (+ i1 x) x2))
         (x5
          (snld23-l-strnlen a1 i1))
         (x6
          (+ x x5))
         (x7
          (snld23-l-strnlen a3 i1))
         (x8
          (+ i1 x)))
      (implies
       (and
        (equal
         (+ x x1)
         (+ x2 x3))
        (equal
         (+ x2
            (snld23-l-strnlen a x4))
         x6)
        (equal
         (+ x1
            (snld23-l-strnlen a2 x4))
         (+ x3 x7))
        (< 0 i1)
        (<= x x2)
        (<=
         (snld23-region
          (snld23-address-base a1))
         0)
        (<=
         (snld23-region
          (snld23-address-base a3))
         0)
        (< x5 x7)
        (<= x2 x8)
        (snld23-linked-p)
        (snld23-sconst-p)
        (snld23-is-uint8-p i2)
        (snld23-is-uint8-p i3)
        (snld23-is-sint32-p result)
        (snld23-is-uint64-p i1)
        (snld23-addr-le-p a1 a)
        (snld23-addr-le-p a3 a2)
        (snld23-valid-bounded-string-p
         a1 i1)
        (snld23-valid-bounded-string-p
         a3 i1)
        (snld23-is-uint64-p x4)
        (snld23-addr-le-p
         a
         (snld23-shift a1 x5))
        (snld23-addr-le-p
         a2
         (snld23-shift a3 x7))
        (snld23-valid-bounded-string-p
         a x4)
        (snld23-valid-bounded-string-p
         a2 x4)
        (if
            (equal x8 x2)
            (equal result 0)
          (and
           (equal
            (snld23-to-uint8
             (snld23-character-memory a))
            i2)
           (equal
            (snld23-to-uint8
             (snld23-character-memory a2))
            i3)
           (if
               (equal i3 i2)
               (and
                (equal result 0)
                (equal i3 0))
             (if
                 (< i3 i2)
                 (equal result -1)
               (equal result 1)))
           (implies
            (equal i2 0)
            (and
             (equal
              x5
              (snld23-l-strlen a1))
             (equal x6 x2)
             (snld23-valid-string-p a1)))
           (implies
            (equal i3 0)
            (and
             (equal
              x7
              (snld23-l-strlen a3))
             (equal
              (+ x x7)
              x2)
             (snld23-valid-string-p a3)))))
        (snld23-prefix-equal-before-p
         a3 a1 x7)
        (snld23-offset-prefix-equal-before-p
         a3 a1 x x2)
        (snld23-uint8-equality-reflects-p
         a3 a1 x7))
       (equal result 1))))))

(value-triple :itpeval-statement-checked)

:q
