;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnchr_Why3_ide_VCstrnchr_loop_inv_5_preserved_goal6:
;; preservation of the strnchr loop length-offset equation after advancing
;; the current address by one, under the stated bounded-string validity,
;; address-order, character-range, and nonmatching-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snrg6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snrg6-address-base (address)
  (car address))

(defun snrg6-address-offset (address)
  (cdr address))

(defun snrg6-shift (address amount)
  (cons
   (snrg6-address-base address)
   (+ (snrg6-address-offset address) amount)))

;; Conservative interfaces represent the arbitrary character memory t_1 and
;; allocation map t, together with the source region, address-order, logical
;; strnlen, C integer conversions, linkedness, and constancy symbols.

(defstub snrg6-character-memory (address) t)
(defstub snrg6-allocation (index) t)
(defstub snrg6-region (base) t)
(defstub snrg6-addr-le-op (left right) t)
(defstub snrg6-addr-lt-op (left right) t)
(defstub snrg6-l-strnlen (address count) t)
(defstub snrg6-to-uint8 (value) t)
(defstub snrg6-to-sint8 (value) t)
(defstub snrg6-to-uint64 (value) t)
(defstub snrg6-to-sint64 (value) t)
(defstub snrg6-linked-op () t)
(defstub snrg6-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snrg6-function-types-p ()
  (forall (address index base count value)
    (and
     (implies
      (snrg6-address-p address)
      (integerp
       (snrg6-character-memory address)))
     (implies
      (and
       (snrg6-address-p address)
       (integerp count))
      (integerp
       (snrg6-l-strnlen address count)))
     (implies
      (integerp index)
      (integerp
       (snrg6-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snrg6-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snrg6-to-uint8 value))
       (integerp
        (snrg6-to-sint8 value))
       (integerp
        (snrg6-to-uint64 value))
       (integerp
        (snrg6-to-sint64 value)))))))

(defun snrg6-addr-le-p (left right)
  (if (snrg6-addr-le-op left right) t nil))

(defun snrg6-addr-lt-p (left right)
  (if (snrg6-addr-lt-op left right) t nil))

;; On equal-base addresses, the source address relations are exactly integer
;; order on offsets.

(defun-sk snrg6-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snrg6-address-p left)
      (snrg6-address-p right)
      (equal
       (snrg6-address-base left)
       (snrg6-address-base right)))
     (and
      (equal
       (snrg6-addr-le-p left right)
       (<=
        (snrg6-address-offset left)
        (snrg6-address-offset right)))
      (equal
       (snrg6-addr-lt-p left right)
       (<
        (snrg6-address-offset left)
        (snrg6-address-offset right)))))))

(defun snrg6-linked-p ()
  (if (snrg6-linked-op) t nil))

(defun snrg6-sconst-p ()
  (if (snrg6-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snrg6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snrg6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snrg6-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun snrg6-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun snrg6-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and the logical strnlen recurrence.

(defun-sk snrg6-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg6-is-uint8-p
       (snrg6-to-uint8 value))
      (implies
       (snrg6-is-uint8-p value)
       (equal
        (snrg6-to-uint8 value)
        value))
      (equal
       (snrg6-to-uint8
        (snrg6-to-uint8 value))
       (snrg6-to-uint8 value))))))

(defun-sk snrg6-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg6-is-sint8-p
       (snrg6-to-sint8 value))
      (implies
       (snrg6-is-sint8-p value)
       (equal
        (snrg6-to-sint8 value)
        value))
      (equal
       (snrg6-to-sint8
        (snrg6-to-sint8 value))
       (snrg6-to-sint8 value))))))

(defun-sk snrg6-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg6-is-uint64-p
       (snrg6-to-uint64 value))
      (implies
       (snrg6-is-uint64-p value)
       (equal
        (snrg6-to-uint64 value)
        value))
      (equal
       (snrg6-to-uint64
        (snrg6-to-uint64 value))
       (snrg6-to-uint64 value))))))

(defun-sk snrg6-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg6-is-sint64-p
       (snrg6-to-sint64 value))
      (implies
       (snrg6-is-sint64-p value)
       (equal
        (snrg6-to-sint64 value)
        value))
      (equal
       (snrg6-to-sint64
        (snrg6-to-sint64 value))
       (snrg6-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk snrg6-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (snrg6-to-sint8
        (snrg6-to-uint8 value))
       (snrg6-to-sint8 value))
      (equal
       (snrg6-to-sint64
        (snrg6-to-uint64 value))
       (snrg6-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snrg6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snrg6-address-base address))
    (<= 0
        (snrg6-address-offset address))
    (<=
     (+ (snrg6-address-offset address)
        length)
     (snrg6-allocation
      (snrg6-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. Its null-position witness stays
;; existentially quantified over all integers, while its character-range
;; condition stays universally quantified over all integers.

(defun-sk snrg6-bounded-string-terminator-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snrg6-character-memory
       (snrg6-shift address index))
      0)
     (< index count)
     (snrg6-is-uint64-p index)
     (snrg6-valid-rw-p
      (snrg6-shift address 0)
      (+ 1 index)))))

(defun-sk snrg6-bounded-string-chars-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snrg6-is-sint8-p
       (snrg6-character-memory
        (snrg6-shift address position)))))))

(defun snrg6-valid-stringn-p (address count)
  (or
   (snrg6-valid-rw-p
    (snrg6-shift address 0)
    (+ 1 count))
   (and
    (snrg6-bounded-string-terminator-p
     address count)
    (snrg6-bounded-string-chars-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snrg6-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snrg6-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snrg6-character-memory
             (snrg6-shift address 0))
            0))
          (equal
           (snrg6-l-strnlen address count)
           0)
        (equal
         (snrg6-to-uint64
          (+ 1
             (snrg6-l-strnlen
              (snrg6-shift address 1)
              (snrg6-to-uint64
               (- count 1)))))
         (snrg6-l-strnlen address count)))
      (snrg6-is-uint64-p
       (snrg6-l-strnlen address count))))))

;; The source loop-invariant hypothesis retains its universal quantifier over
;; every address in the full integer-pair carrier.

(defun-sk snrg6-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snrg6-address-p candidate)
     (implies
      (snrg6-addr-lt-p candidate current)
      (implies
       (snrg6-addr-le-p start candidate)
       (not
        (equal
         (snrg6-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strnchr-loop-inv-5-preserved-goal6-statement ()
  (forall
   (a i1 a1 i)
   (implies
    (and
     (snrg6-address-p a)
     (integerp i1)
     (snrg6-address-p a1)
     (integerp i)
     (snrg6-function-types-p)
     (snrg6-address-order-laws-p)
     (snrg6-to-uint8-laws-p)
     (snrg6-to-sint8-laws-p)
     (snrg6-to-uint64-laws-p)
     (snrg6-to-sint64-laws-p)
     (snrg6-signed-unsigned-projection-laws-p)
     (snrg6-strnlen-laws-p))
    (let*
        ((x
          (snrg6-character-memory a))
         (x1
          (snrg6-to-sint8 i1))
         (x2
          (snrg6-address-offset a1))
         (x3
          (snrg6-address-offset a))
         (x4
          (- (+ i x3) x2))
         (x5
          (snrg6-l-strnlen a1 x4))
         (x6
          (+ x2 x5)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x 0))
        (not (equal x x1))
        (equal
         x6
         (+ x3
            (snrg6-l-strnlen a i)))
        (<= 0 i)
        (<= x2 x3)
        (<=
         (snrg6-region
          (snrg6-address-base a1))
         0)
        (snrg6-linked-p)
        (snrg6-sconst-p)
        (snrg6-is-sint32-p i1)
        (snrg6-is-uint64-p i)
        (snrg6-addr-le-p a1 a)
        (snrg6-is-sint8-p x)
        (snrg6-valid-stringn-p a i)
        (snrg6-is-uint64-p x4)
        (snrg6-valid-stringn-p a1 x4)
        (snrg6-addr-le-p
         a
         (snrg6-shift a1 x5))
        (snrg6-no-earlier-match-p
         a1 a x1))
       (equal
        x6
        (+ 1
           x3
           (snrg6-l-strnlen
            (snrg6-shift a 1)
            (snrg6-to-uint64
             (- i 1))))))))))

(value-triple :itpeval-statement-checked)

:q
