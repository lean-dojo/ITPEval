;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_2_preserved_goal3:
;; preservation of valid-string memory after advancing the current strpbrk
;; pointer by one, under the stated string, address-order, membership,
;; no-match, linkedness, and constancy hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvip3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvip3-address-base (address)
  (car address))

(defun spvip3-address-offset (address)
  (cdr address))

(defun spvip3-shift (address amount)
  (cons
   (spvip3-address-base address)
   (+ (spvip3-address-offset address)
      amount)))

(defun spvip3-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvip3-character-memory (address) t)
(defstub spvip3-allocation (index) t)
(defstub spvip3-region (base) t)
(defstub spvip3-addr-le-op (left right) t)
(defstub spvip3-addr-lt-op (left right) t)
(defstub spvip3-l-strlen (address) t)
(defstub spvip3-l-strpbrk (string accept) t)
(defstub spvip3-to-uint64 (value) t)
(defstub spvip3-linked-op () t)
(defstub spvip3-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvip3-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvip3-address-p address)
      (and
       (integerp
        (spvip3-character-memory address))
       (integerp
        (spvip3-l-strlen address))))
     (implies
      (and
       (spvip3-address-p address)
       (spvip3-address-p other))
      (spvip3-address-p
       (spvip3-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvip3-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvip3-region base)))
     (implies
      (integerp value)
      (integerp
       (spvip3-to-uint64 value))))))

(defun spvip3-addr-le-p (left right)
  (if (spvip3-addr-le-op left right) t nil))

(defun spvip3-addr-lt-p (left right)
  (if (spvip3-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvip3-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvip3-address-p left)
      (spvip3-address-p right)
      (equal
       (spvip3-address-base left)
       (spvip3-address-base right)))
     (and
      (equal
       (spvip3-addr-le-p left right)
       (<=
        (spvip3-address-offset left)
        (spvip3-address-offset right)))
      (equal
       (spvip3-addr-lt-p left right)
       (<
        (spvip3-address-offset left)
        (spvip3-address-offset right)))))))

(defun spvip3-linked-p ()
  (if (spvip3-linked-op) t nil))

(defun spvip3-sconst-p ()
  (if (spvip3-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvip3-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvip3-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvip3-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvip3-is-uint64-p
       (spvip3-to-uint64 value))
      (implies
       (spvip3-is-uint64-p value)
       (equal
        (spvip3-to-uint64 value)
        value))
      (equal
       (spvip3-to-uint64
        (spvip3-to-uint64 value))
       (spvip3-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvip3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvip3-address-base address))
    (<= 0
        (spvip3-address-offset address))
    (<=
     (+ (spvip3-address-offset address)
        length)
     (spvip3-allocation
      (spvip3-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvip3-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvip3-is-sint8-p
       (spvip3-character-memory
        (spvip3-shift address position)))))))

(defun-sk spvip3-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvip3-character-memory
       (spvip3-shift address index))
      0)
     (spvip3-is-uint64-p index)
     (spvip3-valid-rw-p
      (spvip3-shift address 0)
      (+ 1 index))
     (spvip3-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvip3-strlen-laws-p ()
  (forall (address)
    (implies
     (spvip3-address-p address)
     (and
      (if
          (equal
           (spvip3-character-memory
            (spvip3-shift address 0))
           0)
          (equal
           (spvip3-l-strlen address)
           0)
        (equal
         (spvip3-to-uint64
          (+ 1
             (spvip3-l-strlen
              (spvip3-shift address 1))))
         (spvip3-l-strlen address)))
      (spvip3-is-uint64-p
       (spvip3-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvip3-in-array-p (start value)
  (exists (candidate)
    (and
     (spvip3-address-p candidate)
     (equal
      (spvip3-character-memory candidate)
      value)
     (spvip3-addr-le-p start candidate)
     (spvip3-addr-lt-p
      candidate
      (spvip3-shift
       start
       (spvip3-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvip3-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvip3-address-p string)
      (spvip3-address-p accept))
     (and
      (implies
       (equal
        (spvip3-character-memory string)
        0)
       (equal
        (spvip3-l-strpbrk string accept)
        (spvip3-null-address)))
      (implies
       (and
        (not
         (equal
          (spvip3-character-memory string)
          0))
        (spvip3-in-array-p
         accept
         (spvip3-character-memory string)))
       (equal
        (spvip3-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvip3-character-memory string)
          0))
        (not
         (spvip3-in-array-p
          accept
          (spvip3-character-memory string))))
       (equal
        (spvip3-l-strpbrk
         (spvip3-shift string 1)
         accept)
        (spvip3-l-strpbrk string accept)))))))

;; The source's four quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvip3-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvip3-address-p candidate)
     (implies
      (spvip3-addr-lt-p candidate current)
      (implies
       (spvip3-addr-le-p start candidate)
       (not
        (equal
         value
         (spvip3-character-memory candidate))))))))

(defun-sk spvip3-no-x-before-end-p
    (start end value)
  (forall (candidate)
    (implies
     (spvip3-address-p candidate)
     (implies
      (spvip3-addr-le-p start candidate)
      (implies
       (spvip3-addr-lt-p candidate end)
       (not
        (equal
         value
         (spvip3-character-memory candidate))))))))

(defun-sk spvip3-cross-values-distinct-before-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip3-address-p first-candidate)
      (spvip3-address-p second-candidate))
     (implies
      (spvip3-addr-lt-p first-candidate first-current)
      (implies
       (spvip3-addr-le-p second-start second-candidate)
       (implies
        (spvip3-addr-le-p first-start first-candidate)
        (implies
         (spvip3-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip3-character-memory first-candidate)
           (spvip3-character-memory second-candidate))))))))))

(defun-sk spvip3-cross-values-distinct-through-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip3-address-p first-candidate)
      (spvip3-address-p second-candidate))
     (implies
      (spvip3-addr-le-p first-candidate first-current)
      (implies
       (spvip3-addr-le-p second-start second-candidate)
       (implies
        (spvip3-addr-le-p first-start first-candidate)
        (implies
         (spvip3-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip3-character-memory first-candidate)
           (spvip3-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-2-preserved-goal3-statement ()
  (forall
   (a1 a2 a a3)
   (implies
    (and
     (spvip3-address-p a1)
     (spvip3-address-p a2)
     (spvip3-address-p a)
     (spvip3-address-p a3)
     (spvip3-function-types-p)
     (spvip3-address-order-laws-p)
     (spvip3-to-uint64-laws-p)
     (spvip3-strlen-laws-p)
     (spvip3-strpbrk-laws-p))
    (let*
        ((x
          (spvip3-character-memory a1))
         (a4
          (spvip3-shift
           a2
           (spvip3-l-strlen a2)))
         (a5
          (spvip3-shift
           a3
           (spvip3-l-strlen a3))))
      (implies
       (and
        (equal
         (spvip3-character-memory a)
         0)
        (not (equal x 0))
        (equal
         (spvip3-l-strpbrk a3 a2)
         (spvip3-l-strpbrk a1 a2))
        (<=
         (spvip3-region
          (spvip3-address-base a2))
         0)
        (<=
         (spvip3-region
          (spvip3-address-base a3))
         0)
        (spvip3-linked-p)
        (spvip3-sconst-p)
        (spvip3-addr-le-p a2 a)
        (spvip3-addr-le-p a3 a1)
        (spvip3-is-sint8-p x)
        (spvip3-valid-string-p a)
        (spvip3-valid-string-p a1)
        (spvip3-valid-string-p a2)
        (spvip3-valid-string-p a3)
        (spvip3-addr-le-p a a4)
        (spvip3-addr-le-p a1 a5)
        (implies
         (spvip3-in-array-p a2 x)
         (spvip3-in-array-p a x))
        (spvip3-no-x-before-current-p
         a2 a x)
        (spvip3-no-x-before-end-p
         a2 a4 x)
        (spvip3-cross-values-distinct-before-p
         a3 a1 a2 a4)
        (spvip3-cross-values-distinct-through-p
         a3 a1 a2 a4))
       (spvip3-valid-string-p
        (spvip3-shift a1 1)))))))

(value-triple :itpeval-statement-checked)

:q
