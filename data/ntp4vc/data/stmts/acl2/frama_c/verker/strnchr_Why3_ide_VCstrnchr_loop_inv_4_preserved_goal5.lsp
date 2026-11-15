;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnchr_Why3_ide_VCstrnchr_loop_inv_4_preserved_goal5:
;; preservation of bounded-string validity after advancing the current
;; strnchr address, under the stated offset, address-order, character-range,
;; memory-validity, and nonmatching-prefix hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snrg5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snrg5-address-base (address)
  (car address))

(defun snrg5-address-offset (address)
  (cdr address))

(defun snrg5-shift (address amount)
  (cons
   (snrg5-address-base address)
   (+ (snrg5-address-offset address) amount)))

;; Conservative interfaces represent the arbitrary character memory t_1 and
;; allocation map t, together with the source region, address-order, logical
;; strnlen, C integer conversions, linkedness, and constancy symbols.

(defstub snrg5-character-memory (address) t)
(defstub snrg5-allocation (index) t)
(defstub snrg5-region (base) t)
(defstub snrg5-addr-le-op (left right) t)
(defstub snrg5-addr-lt-op (left right) t)
(defstub snrg5-l-strnlen (address count) t)
(defstub snrg5-to-uint8 (value) t)
(defstub snrg5-to-sint8 (value) t)
(defstub snrg5-to-uint64 (value) t)
(defstub snrg5-to-sint64 (value) t)
(defstub snrg5-linked-op () t)
(defstub snrg5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snrg5-function-types-p ()
  (forall (address index base count value)
    (and
     (implies
      (snrg5-address-p address)
      (integerp
       (snrg5-character-memory address)))
     (implies
      (and
       (snrg5-address-p address)
       (integerp count))
      (integerp
       (snrg5-l-strnlen address count)))
     (implies
      (integerp index)
      (integerp
       (snrg5-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snrg5-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snrg5-to-uint8 value))
       (integerp
        (snrg5-to-sint8 value))
       (integerp
        (snrg5-to-uint64 value))
       (integerp
        (snrg5-to-sint64 value)))))))

(defun snrg5-addr-le-p (left right)
  (if (snrg5-addr-le-op left right) t nil))

(defun snrg5-addr-lt-p (left right)
  (if (snrg5-addr-lt-op left right) t nil))

;; On equal-base addresses, the source address relations are exactly integer
;; order on offsets.

(defun-sk snrg5-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snrg5-address-p left)
      (snrg5-address-p right)
      (equal
       (snrg5-address-base left)
       (snrg5-address-base right)))
     (and
      (equal
       (snrg5-addr-le-p left right)
       (<=
        (snrg5-address-offset left)
        (snrg5-address-offset right)))
      (equal
       (snrg5-addr-lt-p left right)
       (<
        (snrg5-address-offset left)
        (snrg5-address-offset right)))))))

(defun snrg5-linked-p ()
  (if (snrg5-linked-op) t nil))

(defun snrg5-sconst-p ()
  (if (snrg5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snrg5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snrg5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snrg5-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun snrg5-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun snrg5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and the logical strnlen recurrence.

(defun-sk snrg5-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg5-is-uint8-p
       (snrg5-to-uint8 value))
      (implies
       (snrg5-is-uint8-p value)
       (equal
        (snrg5-to-uint8 value)
        value))
      (equal
       (snrg5-to-uint8
        (snrg5-to-uint8 value))
       (snrg5-to-uint8 value))))))

(defun-sk snrg5-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg5-is-sint8-p
       (snrg5-to-sint8 value))
      (implies
       (snrg5-is-sint8-p value)
       (equal
        (snrg5-to-sint8 value)
        value))
      (equal
       (snrg5-to-sint8
        (snrg5-to-sint8 value))
       (snrg5-to-sint8 value))))))

(defun-sk snrg5-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg5-is-uint64-p
       (snrg5-to-uint64 value))
      (implies
       (snrg5-is-uint64-p value)
       (equal
        (snrg5-to-uint64 value)
        value))
      (equal
       (snrg5-to-uint64
        (snrg5-to-uint64 value))
       (snrg5-to-uint64 value))))))

(defun-sk snrg5-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snrg5-is-sint64-p
       (snrg5-to-sint64 value))
      (implies
       (snrg5-is-sint64-p value)
       (equal
        (snrg5-to-sint64 value)
        value))
      (equal
       (snrg5-to-sint64
        (snrg5-to-sint64 value))
       (snrg5-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk snrg5-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (snrg5-to-sint8
        (snrg5-to-uint8 value))
       (snrg5-to-sint8 value))
      (equal
       (snrg5-to-sint64
        (snrg5-to-uint64 value))
       (snrg5-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snrg5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snrg5-address-base address))
    (<= 0
        (snrg5-address-offset address))
    (<=
     (+ (snrg5-address-offset address)
        length)
     (snrg5-allocation
      (snrg5-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. Its null-position witness stays
;; existentially quantified over all integers, while its character-range
;; condition stays universally quantified over all integers.

(defun-sk snrg5-bounded-string-terminator-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snrg5-character-memory
       (snrg5-shift address index))
      0)
     (< index count)
     (snrg5-is-uint64-p index)
     (snrg5-valid-rw-p
      (snrg5-shift address 0)
      (+ 1 index)))))

(defun-sk snrg5-bounded-string-chars-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snrg5-is-sint8-p
       (snrg5-character-memory
        (snrg5-shift address position)))))))

(defun snrg5-valid-stringn-p (address count)
  (or
   (snrg5-valid-rw-p
    (snrg5-shift address 0)
    (+ 1 count))
   (and
    (snrg5-bounded-string-terminator-p
     address count)
    (snrg5-bounded-string-chars-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snrg5-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snrg5-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snrg5-character-memory
             (snrg5-shift address 0))
            0))
          (equal
           (snrg5-l-strnlen address count)
           0)
        (equal
         (snrg5-to-uint64
          (+ 1
             (snrg5-l-strnlen
              (snrg5-shift address 1)
              (snrg5-to-uint64
               (- count 1)))))
         (snrg5-l-strnlen address count)))
      (snrg5-is-uint64-p
       (snrg5-l-strnlen address count))))))

;; The source loop-invariant hypothesis retains its universal quantifier over
;; every address in the full integer-pair carrier.

(defun-sk snrg5-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snrg5-address-p candidate)
     (implies
      (snrg5-addr-lt-p candidate current)
      (implies
       (snrg5-addr-le-p start candidate)
       (not
        (equal
         (snrg5-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strnchr-loop-inv-4-preserved-goal5-statement ()
  (forall
   (a i1 a1 i)
   (implies
    (and
     (snrg5-address-p a)
     (integerp i1)
     (snrg5-address-p a1)
     (integerp i)
     (snrg5-function-types-p)
     (snrg5-address-order-laws-p)
     (snrg5-to-uint8-laws-p)
     (snrg5-to-sint8-laws-p)
     (snrg5-to-uint64-laws-p)
     (snrg5-to-sint64-laws-p)
     (snrg5-signed-unsigned-projection-laws-p)
     (snrg5-strnlen-laws-p))
    (let*
        ((x
          (snrg5-character-memory a))
         (x1
          (snrg5-to-sint8 i1))
         (x2
          (snrg5-address-offset a1))
         (x3
          (+ i x2))
         (x4
          (snrg5-address-offset a))
         (x6
          (- (+ i x2) x4))
         (x7
          (snrg5-l-strnlen a1 i)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (not (equal x3 x4))
        (equal
         (+ x4
            (snrg5-l-strnlen a x6))
         (+ x2 x7))
        (<= x2 x4)
        (<=
         (snrg5-region
          (snrg5-address-base a1))
         0)
        (<= x4 x3)
        (snrg5-linked-p)
        (snrg5-sconst-p)
        (snrg5-is-sint32-p i1)
        (snrg5-is-uint64-p i)
        (snrg5-addr-le-p a1 a)
        (snrg5-is-sint8-p x)
        (snrg5-valid-stringn-p a1 i)
        (snrg5-is-uint64-p x6)
        (snrg5-addr-le-p
         a
         (snrg5-shift a1 x7))
        (snrg5-valid-stringn-p a x6)
        (snrg5-no-earlier-match-p
         a1 a x1))
       (snrg5-valid-stringn-p
        (snrg5-shift a 1)
        (snrg5-to-uint64
         (- (- (+ i x2) 1) x4))))))))

(value-triple :itpeval-statement-checked)

:q
