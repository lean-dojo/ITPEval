;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_loop_inv_2_preserved_goal2:
;; preservation of the strchr loop's lower and upper address bounds after
;; advancing the current address by one, under the stated string-validity,
;; address-order, character, linkedness, constancy, and no-earlier-match
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sclp2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sclp2-address-base (address)
  (car address))

(defun sclp2-address-offset (address)
  (cdr address))

(defun sclp2-shift (address amount)
  (cons
   (sclp2-address-base address)
   (+ (sclp2-address-offset address) amount)))

(defun sclp2-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sclp2-character-memory (address) t)
(defstub sclp2-allocation (index) t)
(defstub sclp2-region (base) t)
(defstub sclp2-addr-le-op (left right) t)
(defstub sclp2-addr-lt-op (left right) t)
(defstub sclp2-l-strlen (address) t)
(defstub sclp2-l-strchr (address value) t)
(defstub sclp2-to-uint8 (value) t)
(defstub sclp2-to-sint8 (value) t)
(defstub sclp2-to-uint64 (value) t)
(defstub sclp2-to-sint64 (value) t)
(defstub sclp2-linked-op () t)
(defstub sclp2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sclp2-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sclp2-address-p address)
      (and
       (integerp
        (sclp2-character-memory address))
       (integerp
        (sclp2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sclp2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sclp2-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sclp2-to-uint8 value))
       (integerp
        (sclp2-to-sint8 value))
       (integerp
        (sclp2-to-uint64 value))
       (integerp
        (sclp2-to-sint64 value))))
     (implies
      (and
       (sclp2-address-p address)
       (integerp value))
      (sclp2-address-p
       (sclp2-l-strchr address value))))))

(defun sclp2-addr-le-p (left right)
  (if (sclp2-addr-le-op left right) t nil))

(defun sclp2-addr-lt-p (left right)
  (if (sclp2-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sclp2-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sclp2-address-p left)
      (sclp2-address-p right)
      (equal
       (sclp2-address-base left)
       (sclp2-address-base right)))
     (and
      (equal
       (sclp2-addr-le-p left right)
       (<=
        (sclp2-address-offset left)
        (sclp2-address-offset right)))
      (equal
       (sclp2-addr-lt-p left right)
       (<
        (sclp2-address-offset left)
        (sclp2-address-offset right)))))))

(defun sclp2-linked-p ()
  (if (sclp2-linked-op) t nil))

(defun sclp2-sconst-p ()
  (if (sclp2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sclp2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sclp2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sclp2-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sclp2-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sclp2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrences.

(defun-sk sclp2-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp2-is-uint8-p
       (sclp2-to-uint8 value))
      (implies
       (sclp2-is-uint8-p value)
       (equal
        (sclp2-to-uint8 value)
        value))
      (equal
       (sclp2-to-uint8
        (sclp2-to-uint8 value))
       (sclp2-to-uint8 value))))))

(defun-sk sclp2-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp2-is-sint8-p
       (sclp2-to-sint8 value))
      (implies
       (sclp2-is-sint8-p value)
       (equal
        (sclp2-to-sint8 value)
        value))
      (equal
       (sclp2-to-sint8
        (sclp2-to-sint8 value))
       (sclp2-to-sint8 value))))))

(defun-sk sclp2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp2-is-uint64-p
       (sclp2-to-uint64 value))
      (implies
       (sclp2-is-uint64-p value)
       (equal
        (sclp2-to-uint64 value)
        value))
      (equal
       (sclp2-to-uint64
        (sclp2-to-uint64 value))
       (sclp2-to-uint64 value))))))

(defun-sk sclp2-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp2-is-sint64-p
       (sclp2-to-sint64 value))
      (implies
       (sclp2-is-sint64-p value)
       (equal
        (sclp2-to-sint64 value)
        value))
      (equal
       (sclp2-to-sint64
        (sclp2-to-sint64 value))
       (sclp2-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk sclp2-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sclp2-to-sint8
        (sclp2-to-uint8 value))
       (sclp2-to-sint8 value))
      (equal
       (sclp2-to-sint64
        (sclp2-to-uint64 value))
       (sclp2-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sclp2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sclp2-address-base address))
    (<= 0
        (sclp2-address-offset address))
    (<=
     (+ (sclp2-address-offset address)
        length)
     (sclp2-allocation
      (sclp2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sclp2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sclp2-is-sint8-p
       (sclp2-character-memory
        (sclp2-shift address position)))))))

(defun-sk sclp2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sclp2-character-memory
       (sclp2-shift address index))
      0)
     (sclp2-is-uint64-p index)
     (sclp2-valid-rw-p
      (sclp2-shift address 0)
      (+ 1 index))
     (sclp2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sclp2-strlen-laws-p ()
  (forall (address)
    (implies
     (sclp2-address-p address)
     (and
      (if
          (equal
           (sclp2-character-memory
            (sclp2-shift address 0))
           0)
          (equal
           (sclp2-l-strlen address)
           0)
        (equal
         (sclp2-to-uint64
          (+ 1
             (sclp2-l-strlen
              (sclp2-shift address 1))))
         (sclp2-l-strlen address)))
      (sclp2-is-uint64-p
       (sclp2-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk sclp2-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (sclp2-address-p address)
      (integerp value))
     (if
         (equal
          (sclp2-character-memory address)
          value)
         (equal
          (sclp2-l-strchr address value)
          address)
       (if
           (equal
            (sclp2-character-memory address)
            0)
           (equal
            (sclp2-l-strchr address value)
            (sclp2-null-address))
         (equal
          (sclp2-l-strchr
           (sclp2-shift address 1)
           value)
          (sclp2-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sclp2-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sclp2-address-p candidate)
     (implies
      (sclp2-addr-lt-p candidate current)
      (implies
       (sclp2-addr-le-p start candidate)
       (not
        (equal
         (sclp2-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchr-loop-inv-2-preserved-goal2-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (sclp2-address-p a)
     (integerp i)
     (sclp2-address-p a1)
     (sclp2-function-types-p)
     (sclp2-address-order-laws-p)
     (sclp2-to-uint8-laws-p)
     (sclp2-to-sint8-laws-p)
     (sclp2-to-uint64-laws-p)
     (sclp2-to-sint64-laws-p)
     (sclp2-signed-unsigned-projection-laws-p)
     (sclp2-strlen-laws-p)
     (sclp2-strchr-law-p))
    (let*
        ((x
          (sclp2-character-memory a))
         (x1
          (sclp2-to-sint8 i))
         (a2
          (sclp2-shift
           a1
           (sclp2-l-strlen a1)))
         (a3
          (sclp2-shift a 1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (sclp2-l-strchr a1 x1)
         (sclp2-l-strchr a x1))
        (<=
         (sclp2-region
          (sclp2-address-base a1))
         0)
        (sclp2-linked-p)
        (sclp2-sconst-p)
        (sclp2-is-sint32-p i)
        (sclp2-addr-le-p a1 a)
        (sclp2-is-sint8-p x)
        (sclp2-valid-string-p a)
        (sclp2-valid-string-p a1)
        (sclp2-addr-le-p a a2)
        (sclp2-no-earlier-match-p
         a1 a x1))
       (and
        (sclp2-addr-le-p a1 a3)
        (sclp2-addr-le-p a3 a2)))))))

(value-triple :itpeval-statement-checked)

:q
