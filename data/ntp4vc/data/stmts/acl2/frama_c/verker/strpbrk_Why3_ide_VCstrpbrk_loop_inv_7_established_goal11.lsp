;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_7_established_goal11:
;; establishment of the strpbrk loop invariant that the selected accept
;; address contains a byte distinct from the current source byte, under the
;; stated string, address-order, and quantified no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvi7e11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvi7e11-address-base (address)
  (car address))

(defun spvi7e11-address-offset (address)
  (cdr address))

(defun spvi7e11-shift (address amount)
  (cons
   (spvi7e11-address-base address)
   (+ (spvi7e11-address-offset address)
      amount)))

(defun spvi7e11-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvi7e11-character-memory (address) t)
(defstub spvi7e11-allocation (index) t)
(defstub spvi7e11-region (base) t)
(defstub spvi7e11-addr-le-op (left right) t)
(defstub spvi7e11-addr-lt-op (left right) t)
(defstub spvi7e11-l-strlen (address) t)
(defstub spvi7e11-l-strpbrk (string accept) t)
(defstub spvi7e11-to-uint64 (value) t)
(defstub spvi7e11-linked-op () t)
(defstub spvi7e11-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvi7e11-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvi7e11-address-p address)
      (and
       (integerp
        (spvi7e11-character-memory address))
       (integerp
        (spvi7e11-l-strlen address))))
     (implies
      (and
       (spvi7e11-address-p address)
       (spvi7e11-address-p other))
      (spvi7e11-address-p
       (spvi7e11-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvi7e11-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvi7e11-region base)))
     (implies
      (integerp value)
      (integerp
       (spvi7e11-to-uint64 value))))))

(defun spvi7e11-addr-le-p (left right)
  (if (spvi7e11-addr-le-op left right) t nil))

(defun spvi7e11-addr-lt-p (left right)
  (if (spvi7e11-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvi7e11-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvi7e11-address-p left)
      (spvi7e11-address-p right)
      (equal
       (spvi7e11-address-base left)
       (spvi7e11-address-base right)))
     (and
      (equal
       (spvi7e11-addr-le-p left right)
       (<=
        (spvi7e11-address-offset left)
        (spvi7e11-address-offset right)))
      (equal
       (spvi7e11-addr-lt-p left right)
       (<
        (spvi7e11-address-offset left)
        (spvi7e11-address-offset right)))))))

(defun spvi7e11-linked-p ()
  (if (spvi7e11-linked-op) t nil))

(defun spvi7e11-sconst-p ()
  (if (spvi7e11-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvi7e11-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvi7e11-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvi7e11-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvi7e11-is-uint64-p
       (spvi7e11-to-uint64 value))
      (implies
       (spvi7e11-is-uint64-p value)
       (equal
        (spvi7e11-to-uint64 value)
        value))
      (equal
       (spvi7e11-to-uint64
        (spvi7e11-to-uint64 value))
       (spvi7e11-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvi7e11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvi7e11-address-base address))
    (<= 0
        (spvi7e11-address-offset address))
    (<=
     (+ (spvi7e11-address-offset address)
        length)
     (spvi7e11-allocation
      (spvi7e11-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvi7e11-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvi7e11-is-sint8-p
       (spvi7e11-character-memory
        (spvi7e11-shift address position)))))))

(defun-sk spvi7e11-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvi7e11-character-memory
       (spvi7e11-shift address index))
      0)
     (spvi7e11-is-uint64-p index)
     (spvi7e11-valid-rw-p
      (spvi7e11-shift address 0)
      (+ 1 index))
     (spvi7e11-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvi7e11-strlen-laws-p ()
  (forall (address)
    (implies
     (spvi7e11-address-p address)
     (and
      (if
          (equal
           (spvi7e11-character-memory
            (spvi7e11-shift address 0))
           0)
          (equal
           (spvi7e11-l-strlen address)
           0)
        (equal
         (spvi7e11-to-uint64
          (+ 1
             (spvi7e11-l-strlen
              (spvi7e11-shift address 1))))
         (spvi7e11-l-strlen address)))
      (spvi7e11-is-uint64-p
       (spvi7e11-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvi7e11-in-array-p (start value)
  (exists (candidate)
    (and
     (spvi7e11-address-p candidate)
     (equal
      (spvi7e11-character-memory candidate)
      value)
     (spvi7e11-addr-le-p start candidate)
     (spvi7e11-addr-lt-p
      candidate
      (spvi7e11-shift
       start
       (spvi7e11-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvi7e11-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvi7e11-address-p string)
      (spvi7e11-address-p accept))
     (and
      (implies
       (equal
        (spvi7e11-character-memory string)
        0)
       (equal
        (spvi7e11-l-strpbrk string accept)
        (spvi7e11-null-address)))
      (implies
       (and
        (not
         (equal
          (spvi7e11-character-memory string)
          0))
        (spvi7e11-in-array-p
         accept
         (spvi7e11-character-memory string)))
       (equal
        (spvi7e11-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvi7e11-character-memory string)
          0))
        (not
         (spvi7e11-in-array-p
          accept
          (spvi7e11-character-memory string))))
       (equal
        (spvi7e11-l-strpbrk
         (spvi7e11-shift string 1)
         accept)
        (spvi7e11-l-strpbrk string accept)))))))

;; The source's final no-match hypothesis remains universal over both address
;; variables and over the complete integer-pair address domain.

(defun-sk spvi7e11-cross-values-distinct-p
    (first-start second-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvi7e11-address-p first-candidate)
      (spvi7e11-address-p second-candidate))
     (implies
      (spvi7e11-addr-lt-p first-candidate first-current)
      (implies
       (spvi7e11-addr-le-p second-start second-candidate)
       (implies
        (spvi7e11-addr-le-p first-start first-candidate)
        (implies
         (spvi7e11-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvi7e11-character-memory first-candidate)
           (spvi7e11-character-memory second-candidate))))))))))

(defun-sk ntp4vc-strpbrk-loop-inv-7-established-goal11-statement ()
  (forall
   (a a2 a1 a3)
   (implies
    (and
     (spvi7e11-address-p a)
     (spvi7e11-address-p a2)
     (spvi7e11-address-p a1)
     (spvi7e11-address-p a3)
     (spvi7e11-function-types-p)
     (spvi7e11-address-order-laws-p)
     (spvi7e11-to-uint64-laws-p)
     (spvi7e11-strlen-laws-p)
     (spvi7e11-strpbrk-laws-p))
    (let
        ((x
          (spvi7e11-character-memory a)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (spvi7e11-l-strpbrk a2 a1)
         (spvi7e11-l-strpbrk a a1))
        (<=
         (spvi7e11-region
          (spvi7e11-address-base a1))
         0)
        (<=
         (spvi7e11-region
          (spvi7e11-address-base a2))
         0)
        (spvi7e11-linked-p)
        (spvi7e11-sconst-p)
        (spvi7e11-addr-lt-p a3 a1)
        (spvi7e11-addr-le-p a1 a3)
        (spvi7e11-addr-le-p a2 a)
        (spvi7e11-is-sint8-p x)
        (spvi7e11-valid-string-p a)
        (spvi7e11-valid-string-p a1)
        (spvi7e11-valid-string-p a2)
        (spvi7e11-addr-le-p
         a
         (spvi7e11-shift
          a2
          (spvi7e11-l-strlen a2)))
        (spvi7e11-cross-values-distinct-p
         a2
         a1
         a
         (spvi7e11-shift
          a1
          (spvi7e11-l-strlen a1))))
       (not
        (equal
         (spvi7e11-character-memory a3)
         x)))))))

(value-triple :itpeval-statement-checked)

:q
