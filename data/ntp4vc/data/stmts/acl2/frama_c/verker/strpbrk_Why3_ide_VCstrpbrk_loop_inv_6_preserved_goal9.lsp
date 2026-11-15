;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_6_preserved_goal9:
;; preservation of valid-string memory after advancing the current strpbrk
;; pointer by one, under the stated string, byte-range, address-order,
;; membership, no-match, linkedness, and constancy hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvi6g9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvi6g9-address-base (address)
  (car address))

(defun spvi6g9-address-offset (address)
  (cdr address))

(defun spvi6g9-shift (address amount)
  (cons
   (spvi6g9-address-base address)
   (+ (spvi6g9-address-offset address)
      amount)))

(defun spvi6g9-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvi6g9-character-memory (address) t)
(defstub spvi6g9-allocation (index) t)
(defstub spvi6g9-region (base) t)
(defstub spvi6g9-addr-le-op (left right) t)
(defstub spvi6g9-addr-lt-op (left right) t)
(defstub spvi6g9-l-strlen (address) t)
(defstub spvi6g9-l-strpbrk (string accept) t)
(defstub spvi6g9-to-uint64 (value) t)
(defstub spvi6g9-linked-op () t)
(defstub spvi6g9-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvi6g9-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvi6g9-address-p address)
      (and
       (integerp
        (spvi6g9-character-memory address))
       (integerp
        (spvi6g9-l-strlen address))))
     (implies
      (and
       (spvi6g9-address-p address)
       (spvi6g9-address-p other))
      (spvi6g9-address-p
       (spvi6g9-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvi6g9-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvi6g9-region base)))
     (implies
      (integerp value)
      (integerp
       (spvi6g9-to-uint64 value))))))

(defun spvi6g9-addr-le-p (left right)
  (if (spvi6g9-addr-le-op left right) t nil))

(defun spvi6g9-addr-lt-p (left right)
  (if (spvi6g9-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvi6g9-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvi6g9-address-p left)
      (spvi6g9-address-p right)
      (equal
       (spvi6g9-address-base left)
       (spvi6g9-address-base right)))
     (and
      (equal
       (spvi6g9-addr-le-p left right)
       (<=
        (spvi6g9-address-offset left)
        (spvi6g9-address-offset right)))
      (equal
       (spvi6g9-addr-lt-p left right)
       (<
        (spvi6g9-address-offset left)
        (spvi6g9-address-offset right)))))))

(defun spvi6g9-linked-p ()
  (if (spvi6g9-linked-op) t nil))

(defun spvi6g9-sconst-p ()
  (if (spvi6g9-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvi6g9-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvi6g9-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvi6g9-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvi6g9-is-uint64-p
       (spvi6g9-to-uint64 value))
      (implies
       (spvi6g9-is-uint64-p value)
       (equal
        (spvi6g9-to-uint64 value)
        value))
      (equal
       (spvi6g9-to-uint64
        (spvi6g9-to-uint64 value))
       (spvi6g9-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvi6g9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvi6g9-address-base address))
    (<= 0
        (spvi6g9-address-offset address))
    (<=
     (+ (spvi6g9-address-offset address)
        length)
     (spvi6g9-allocation
      (spvi6g9-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvi6g9-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvi6g9-is-sint8-p
       (spvi6g9-character-memory
        (spvi6g9-shift address position)))))))

(defun-sk spvi6g9-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvi6g9-character-memory
       (spvi6g9-shift address index))
      0)
     (spvi6g9-is-uint64-p index)
     (spvi6g9-valid-rw-p
      (spvi6g9-shift address 0)
      (+ 1 index))
     (spvi6g9-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvi6g9-strlen-laws-p ()
  (forall (address)
    (implies
     (spvi6g9-address-p address)
     (and
      (if
          (equal
           (spvi6g9-character-memory
            (spvi6g9-shift address 0))
           0)
          (equal
           (spvi6g9-l-strlen address)
           0)
        (equal
         (spvi6g9-to-uint64
          (+ 1
             (spvi6g9-l-strlen
              (spvi6g9-shift address 1))))
         (spvi6g9-l-strlen address)))
      (spvi6g9-is-uint64-p
       (spvi6g9-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvi6g9-in-array-p (start value)
  (exists (candidate)
    (and
     (spvi6g9-address-p candidate)
     (equal
      (spvi6g9-character-memory candidate)
      value)
     (spvi6g9-addr-le-p start candidate)
     (spvi6g9-addr-lt-p
      candidate
      (spvi6g9-shift
       start
       (spvi6g9-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvi6g9-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvi6g9-address-p string)
      (spvi6g9-address-p accept))
     (and
      (implies
       (equal
        (spvi6g9-character-memory string)
        0)
       (equal
        (spvi6g9-l-strpbrk string accept)
        (spvi6g9-null-address)))
      (implies
       (and
        (not
         (equal
          (spvi6g9-character-memory string)
          0))
        (spvi6g9-in-array-p
         accept
         (spvi6g9-character-memory string)))
       (equal
        (spvi6g9-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvi6g9-character-memory string)
          0))
        (not
         (spvi6g9-in-array-p
          accept
          (spvi6g9-character-memory string))))
       (equal
        (spvi6g9-l-strpbrk
         (spvi6g9-shift string 1)
         accept)
        (spvi6g9-l-strpbrk string accept)))))))

;; The source's two quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvi6g9-no-value-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvi6g9-address-p candidate)
     (implies
      (spvi6g9-addr-lt-p candidate current)
      (implies
       (spvi6g9-addr-le-p start candidate)
       (not
        (equal
         value
         (spvi6g9-character-memory candidate))))))))

(defun-sk spvi6g9-cross-values-distinct-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvi6g9-address-p first-candidate)
      (spvi6g9-address-p second-candidate))
     (implies
      (spvi6g9-addr-lt-p first-candidate first-current)
      (implies
       (spvi6g9-addr-le-p second-start second-candidate)
       (implies
        (spvi6g9-addr-le-p first-start first-candidate)
        (implies
         (spvi6g9-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvi6g9-character-memory first-candidate)
           (spvi6g9-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-6-preserved-goal9-statement ()
  (forall
   (a a1 a2 a3)
   (implies
    (and
     (spvi6g9-address-p a)
     (spvi6g9-address-p a1)
     (spvi6g9-address-p a2)
     (spvi6g9-address-p a3)
     (spvi6g9-function-types-p)
     (spvi6g9-address-order-laws-p)
     (spvi6g9-to-uint64-laws-p)
     (spvi6g9-strlen-laws-p)
     (spvi6g9-strpbrk-laws-p))
    (let*
        ((x
          (spvi6g9-character-memory a))
         (x1
          (spvi6g9-character-memory a1))
         (a4
          (spvi6g9-shift
           a2
           (spvi6g9-l-strlen a2))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (spvi6g9-l-strpbrk a3 a2)
         (spvi6g9-l-strpbrk a1 a2))
        (<=
         (spvi6g9-region
          (spvi6g9-address-base a2))
         0)
        (<=
         (spvi6g9-region
          (spvi6g9-address-base a3))
         0)
        (spvi6g9-linked-p)
        (spvi6g9-sconst-p)
        (spvi6g9-addr-le-p a2 a)
        (spvi6g9-addr-le-p a3 a1)
        (spvi6g9-is-sint8-p x)
        (spvi6g9-is-sint8-p x1)
        (spvi6g9-valid-string-p a)
        (spvi6g9-valid-string-p a1)
        (spvi6g9-valid-string-p a2)
        (spvi6g9-valid-string-p a3)
        (spvi6g9-addr-le-p a a4)
        (spvi6g9-addr-le-p
         a1
         (spvi6g9-shift
          a3
          (spvi6g9-l-strlen a3)))
        (implies
         (spvi6g9-in-array-p a2 x1)
         (spvi6g9-in-array-p a x1))
        (spvi6g9-no-value-before-current-p
         a2 a x1)
        (spvi6g9-cross-values-distinct-p
         a3 a1 a2 a4))
       (spvi6g9-valid-string-p
        (spvi6g9-shift a 1)))))))

(value-triple :itpeval-statement-checked)

:q
