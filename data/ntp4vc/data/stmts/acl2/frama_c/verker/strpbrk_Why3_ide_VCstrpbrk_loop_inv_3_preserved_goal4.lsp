;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_3_preserved_goal4:
;; preservation of the strpbrk loop invariant that two constrained memory
;; positions contain distinct bytes under the stated string, address-order,
;; membership, and quantified no-match hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvip4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvip4-address-base (address)
  (car address))

(defun spvip4-address-offset (address)
  (cdr address))

(defun spvip4-shift (address amount)
  (cons
   (spvip4-address-base address)
   (+ (spvip4-address-offset address)
      amount)))

(defun spvip4-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, C integer conversions,
;; linkedness, and constancy symbols.

(defstub spvip4-character-memory (address) t)
(defstub spvip4-allocation (index) t)
(defstub spvip4-region (base) t)
(defstub spvip4-addr-le-op (left right) t)
(defstub spvip4-addr-lt-op (left right) t)
(defstub spvip4-l-strlen (address) t)
(defstub spvip4-l-strpbrk (string accept) t)
(defstub spvip4-to-uint64 (value) t)
(defstub spvip4-to-sint64 (value) t)
(defstub spvip4-linked-op () t)
(defstub spvip4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvip4-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvip4-address-p address)
      (and
       (integerp
        (spvip4-character-memory address))
       (integerp
        (spvip4-l-strlen address))))
     (implies
      (and
       (spvip4-address-p address)
       (spvip4-address-p other))
      (spvip4-address-p
       (spvip4-l-strpbrk address other)))
     (implies
     (integerp index)
      (integerp
       (spvip4-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvip4-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (spvip4-to-uint64 value))
       (integerp
        (spvip4-to-sint64 value)))))))

(defun spvip4-addr-le-p (left right)
  (if (spvip4-addr-le-op left right) t nil))

(defun spvip4-addr-lt-p (left right)
  (if (spvip4-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvip4-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvip4-address-p left)
      (spvip4-address-p right)
      (equal
       (spvip4-address-base left)
       (spvip4-address-base right)))
     (and
      (equal
       (spvip4-addr-le-p left right)
       (<=
        (spvip4-address-offset left)
        (spvip4-address-offset right)))
      (equal
       (spvip4-addr-lt-p left right)
       (<
        (spvip4-address-offset left)
        (spvip4-address-offset right)))))))

(defun spvip4-linked-p ()
  (if (spvip4-linked-op) t nil))

(defun spvip4-sconst-p ()
  (if (spvip4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvip4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvip4-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun spvip4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract 64-bit C integer conversions.

(defun-sk spvip4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvip4-is-uint64-p
       (spvip4-to-uint64 value))
      (implies
       (spvip4-is-uint64-p value)
       (equal
        (spvip4-to-uint64 value)
        value))
      (equal
       (spvip4-to-uint64
        (spvip4-to-uint64 value))
       (spvip4-to-uint64 value))))))

(defun-sk spvip4-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvip4-is-sint64-p
       (spvip4-to-sint64 value))
      (implies
       (spvip4-is-sint64-p value)
       (equal
        (spvip4-to-sint64 value)
        value))
      (equal
       (spvip4-to-sint64
        (spvip4-to-sint64 value))
       (spvip4-to-sint64 value))))))

;; Exact Cint.proj_int64 interaction between signed and unsigned conversion.

(defun-sk spvip4-signed-unsigned-projection-law-p ()
  (forall (value)
    (implies
     (integerp value)
     (equal
      (spvip4-to-sint64
       (spvip4-to-uint64 value))
      (spvip4-to-sint64 value)))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvip4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvip4-address-base address))
    (<= 0
        (spvip4-address-offset address))
    (<=
     (+ (spvip4-address-offset address)
        length)
     (spvip4-allocation
      (spvip4-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvip4-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvip4-is-sint8-p
       (spvip4-character-memory
        (spvip4-shift address position)))))))

(defun-sk spvip4-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvip4-character-memory
       (spvip4-shift address index))
      0)
     (spvip4-is-uint64-p index)
     (spvip4-valid-rw-p
      (spvip4-shift address 0)
      (+ 1 index))
     (spvip4-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvip4-strlen-laws-p ()
  (forall (address)
    (implies
     (spvip4-address-p address)
     (and
      (if
          (equal
           (spvip4-character-memory
            (spvip4-shift address 0))
           0)
          (equal
           (spvip4-l-strlen address)
           0)
        (equal
         (spvip4-to-uint64
          (+ 1
             (spvip4-l-strlen
              (spvip4-shift address 1))))
         (spvip4-l-strlen address)))
      (spvip4-is-uint64-p
       (spvip4-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvip4-in-array-p (start value)
  (exists (candidate)
    (and
     (spvip4-address-p candidate)
     (equal
      (spvip4-character-memory candidate)
      value)
     (spvip4-addr-le-p start candidate)
     (spvip4-addr-lt-p
      candidate
      (spvip4-shift
       start
       (spvip4-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvip4-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvip4-address-p string)
      (spvip4-address-p accept))
     (and
      (implies
       (equal
        (spvip4-character-memory string)
        0)
       (equal
        (spvip4-l-strpbrk string accept)
        (spvip4-null-address)))
      (implies
       (and
        (not
         (equal
          (spvip4-character-memory string)
          0))
        (spvip4-in-array-p
         accept
         (spvip4-character-memory string)))
       (equal
        (spvip4-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvip4-character-memory string)
          0))
        (not
         (spvip4-in-array-p
          accept
          (spvip4-character-memory string))))
       (equal
        (spvip4-l-strpbrk
         (spvip4-shift string 1)
         accept)
        (spvip4-l-strpbrk string accept)))))))

;; The source's four quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvip4-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvip4-address-p candidate)
     (implies
      (spvip4-addr-lt-p candidate current)
      (implies
       (spvip4-addr-le-p start candidate)
       (not
        (equal
         value
         (spvip4-character-memory candidate))))))))

(defun-sk spvip4-no-x-before-end-p
    (start end value)
  (forall (candidate)
    (implies
     (spvip4-address-p candidate)
     (implies
      (spvip4-addr-le-p start candidate)
      (implies
       (spvip4-addr-lt-p candidate end)
       (not
        (equal
         value
         (spvip4-character-memory candidate))))))))

(defun-sk spvip4-cross-values-distinct-before-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip4-address-p first-candidate)
      (spvip4-address-p second-candidate))
     (implies
      (spvip4-addr-lt-p first-candidate first-current)
      (implies
       (spvip4-addr-le-p second-start second-candidate)
       (implies
        (spvip4-addr-le-p first-start first-candidate)
        (implies
         (spvip4-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip4-character-memory first-candidate)
           (spvip4-character-memory second-candidate))))))))))

(defun-sk spvip4-cross-values-distinct-through-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip4-address-p first-candidate)
      (spvip4-address-p second-candidate))
     (implies
      (spvip4-addr-le-p first-candidate first-current)
      (implies
       (spvip4-addr-le-p second-start second-candidate)
       (implies
        (spvip4-addr-le-p first-start first-candidate)
        (implies
         (spvip4-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip4-character-memory first-candidate)
           (spvip4-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-3-preserved-goal4-statement ()
  (forall
   (a1 a2 a a3 a4 a5)
   (implies
    (and
     (spvip4-address-p a1)
     (spvip4-address-p a2)
     (spvip4-address-p a)
     (spvip4-address-p a3)
     (spvip4-address-p a4)
     (spvip4-address-p a5)
     (spvip4-function-types-p)
     (spvip4-address-order-laws-p)
     (spvip4-to-uint64-laws-p)
     (spvip4-to-sint64-laws-p)
     (spvip4-signed-unsigned-projection-law-p)
     (spvip4-strlen-laws-p)
     (spvip4-strpbrk-laws-p))
    (let*
        ((x
          (spvip4-character-memory a1))
         (a6
          (spvip4-shift
           a2
           (spvip4-l-strlen a2))))
      (implies
       (and
        (equal
         (spvip4-character-memory a)
         0)
        (not (equal x 0))
        (equal
         (spvip4-l-strpbrk a3 a2)
         (spvip4-l-strpbrk a1 a2))
        (<=
         (spvip4-region
          (spvip4-address-base a2))
         0)
        (<=
         (spvip4-region
          (spvip4-address-base a3))
         0)
        (spvip4-linked-p)
        (spvip4-sconst-p)
        (spvip4-addr-le-p a2 a)
        (spvip4-addr-le-p a2 a4)
        (spvip4-addr-le-p a3 a1)
        (spvip4-addr-le-p a3 a5)
        (spvip4-is-sint8-p x)
        (spvip4-valid-string-p a)
        (spvip4-valid-string-p a1)
        (spvip4-valid-string-p a2)
        (spvip4-valid-string-p a3)
        (spvip4-addr-lt-p
         a5
         (spvip4-shift a1 1))
        (spvip4-addr-lt-p a4 a6)
        (spvip4-addr-le-p a a6)
        (spvip4-addr-le-p
         a1
         (spvip4-shift
          a3
          (spvip4-l-strlen a3)))
        (implies
         (spvip4-in-array-p a2 x)
         (spvip4-in-array-p a x))
        (spvip4-no-x-before-current-p
         a2 a x)
        (spvip4-no-x-before-end-p
         a2 a6 x)
        (spvip4-cross-values-distinct-before-p
         a3 a1 a2 a6)
        (spvip4-cross-values-distinct-through-p
         a3 a1 a2 a6))
       (not
        (equal
         (spvip4-character-memory a5)
         (spvip4-character-memory a4))))))))

(value-triple :itpeval-statement-checked)

:q
