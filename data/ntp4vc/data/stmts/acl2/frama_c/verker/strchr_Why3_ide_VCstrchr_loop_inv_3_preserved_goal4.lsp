;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_loop_inv_3_preserved_goal4:
;; preservation of the strchr loop invariant stating that the character at
;; the constrained current address differs from the searched signed byte.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slg4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slg4-address-base (address)
  (car address))

(defun slg4-address-offset (address)
  (cdr address))

(defun slg4-shift (address amount)
  (cons
   (slg4-address-base address)
   (+ (slg4-address-offset address) amount)))

(defun slg4-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub slg4-character-memory (address) t)
(defstub slg4-allocation (index) t)
(defstub slg4-region (base) t)
(defstub slg4-addr-le-op (left right) t)
(defstub slg4-addr-lt-op (left right) t)
(defstub slg4-l-strlen (address) t)
(defstub slg4-l-strchr (address value) t)
(defstub slg4-to-uint8 (value) t)
(defstub slg4-to-sint8 (value) t)
(defstub slg4-to-uint64 (value) t)
(defstub slg4-to-sint64 (value) t)
(defstub slg4-linked-op () t)
(defstub slg4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk slg4-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (slg4-address-p address)
      (and
       (integerp
        (slg4-character-memory address))
       (integerp
        (slg4-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (slg4-allocation index)))
     (implies
      (integerp base)
      (integerp
       (slg4-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (slg4-to-uint8 value))
       (integerp
        (slg4-to-sint8 value))
       (integerp
        (slg4-to-uint64 value))
       (integerp
        (slg4-to-sint64 value))))
     (implies
      (and
       (slg4-address-p address)
       (integerp value))
      (slg4-address-p
       (slg4-l-strchr address value))))))

(defun slg4-addr-le-p (left right)
  (if (slg4-addr-le-op left right) t nil))

(defun slg4-addr-lt-p (left right)
  (if (slg4-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk slg4-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (slg4-address-p left)
      (slg4-address-p right)
      (equal
       (slg4-address-base left)
       (slg4-address-base right)))
     (and
      (equal
       (slg4-addr-le-p left right)
       (<=
        (slg4-address-offset left)
        (slg4-address-offset right)))
      (equal
       (slg4-addr-lt-p left right)
       (<
        (slg4-address-offset left)
        (slg4-address-offset right)))))))

(defun slg4-linked-p ()
  (if (slg4-linked-op) t nil))

(defun slg4-sconst-p ()
  (if (slg4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun slg4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun slg4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun slg4-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun slg4-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun slg4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the VC and its logical string recurrences.

(defun-sk slg4-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg4-is-uint8-p
       (slg4-to-uint8 value))
      (implies
       (slg4-is-uint8-p value)
       (equal
        (slg4-to-uint8 value)
        value))
      (equal
       (slg4-to-uint8
        (slg4-to-uint8 value))
       (slg4-to-uint8 value))))))

(defun-sk slg4-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg4-is-sint8-p
       (slg4-to-sint8 value))
      (implies
       (slg4-is-sint8-p value)
       (equal
        (slg4-to-sint8 value)
        value))
      (equal
       (slg4-to-sint8
        (slg4-to-sint8 value))
       (slg4-to-sint8 value))))))

(defun-sk slg4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg4-is-uint64-p
       (slg4-to-uint64 value))
      (implies
       (slg4-is-uint64-p value)
       (equal
        (slg4-to-uint64 value)
        value))
      (equal
       (slg4-to-uint64
        (slg4-to-uint64 value))
       (slg4-to-uint64 value))))))

(defun-sk slg4-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg4-is-sint64-p
       (slg4-to-sint64 value))
      (implies
       (slg4-is-sint64-p value)
       (equal
        (slg4-to-sint64 value)
        value))
      (equal
       (slg4-to-sint64
        (slg4-to-sint64 value))
       (slg4-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk slg4-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (slg4-to-sint8
        (slg4-to-uint8 value))
       (slg4-to-sint8 value))
      (equal
       (slg4-to-sint64
        (slg4-to-uint64 value))
       (slg4-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun slg4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (slg4-address-base address))
    (<= 0
        (slg4-address-offset address))
    (<=
     (+ (slg4-address-offset address)
        length)
     (slg4-allocation
      (slg4-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk slg4-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (slg4-is-sint8-p
       (slg4-character-memory
        (slg4-shift address position)))))))

(defun-sk slg4-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (slg4-character-memory
       (slg4-shift address index))
      0)
     (slg4-is-uint64-p index)
     (slg4-valid-rw-p
      (slg4-shift address 0)
      (+ 1 index))
     (slg4-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk slg4-strlen-laws-p ()
  (forall (address)
    (implies
     (slg4-address-p address)
     (and
      (if
          (equal
           (slg4-character-memory
            (slg4-shift address 0))
           0)
          (equal
           (slg4-l-strlen address)
           0)
        (equal
         (slg4-to-uint64
          (+ 1
             (slg4-l-strlen
              (slg4-shift address 1))))
         (slg4-l-strlen address)))
      (slg4-is-uint64-p
       (slg4-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk slg4-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (slg4-address-p address)
      (integerp value))
     (if
         (equal
          (slg4-character-memory address)
          value)
         (equal
          (slg4-l-strchr address value)
          address)
       (if
           (equal
            (slg4-character-memory address)
            0)
           (equal
            (slg4-l-strchr address value)
            (slg4-null-address))
         (equal
          (slg4-l-strchr
           (slg4-shift address 1)
           value)
          (slg4-l-strchr address value)))))))

;; The source loop-invariant hypothesis retains its universal quantifier over
;; every address rather than restricting the address carrier.

(defun-sk slg4-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (slg4-address-p candidate)
     (implies
      (slg4-addr-lt-p candidate current)
      (implies
       (slg4-addr-le-p start candidate)
       (not
        (equal
         (slg4-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchr-loop-inv-3-preserved-goal4-statement ()
  (forall
   (a i a1 a2)
   (implies
    (and
     (slg4-address-p a)
     (integerp i)
     (slg4-address-p a1)
     (slg4-address-p a2)
     (slg4-function-types-p)
     (slg4-address-order-laws-p)
     (slg4-to-uint8-laws-p)
     (slg4-to-sint8-laws-p)
     (slg4-to-uint64-laws-p)
     (slg4-to-sint64-laws-p)
     (slg4-signed-unsigned-projection-laws-p)
     (slg4-strlen-laws-p)
     (slg4-strchr-law-p))
    (let*
        ((x
          (slg4-character-memory a))
         (x1
          (slg4-to-sint8 i)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (slg4-l-strchr a1 x1)
         (slg4-l-strchr a x1))
        (<=
         (slg4-region
          (slg4-address-base a1))
         0)
        (slg4-linked-p)
        (slg4-sconst-p)
        (slg4-is-sint32-p i)
        (slg4-addr-le-p a1 a)
        (slg4-addr-le-p a1 a2)
        (slg4-is-sint8-p x)
        (slg4-valid-string-p a)
        (slg4-valid-string-p a1)
        (slg4-addr-lt-p
         a2
         (slg4-shift a 1))
        (slg4-addr-le-p
         a
         (slg4-shift
          a1
          (slg4-l-strlen a1)))
        (slg4-no-earlier-match-p
         a1 a x1))
       (not
        (equal
         (slg4-character-memory a2)
         x1)))))))

(value-triple :itpeval-statement-checked)

:q
