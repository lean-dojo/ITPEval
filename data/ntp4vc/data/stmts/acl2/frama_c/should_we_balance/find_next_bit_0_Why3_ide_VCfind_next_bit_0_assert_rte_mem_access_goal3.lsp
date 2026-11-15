;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3:
;; readability of the next byte in a shifted address range under the stated
;; index bounds, integer ranges, allocation validity, linking, region, and
;; quantified zero-prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun fnb3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fnb3-address-base (address)
  (car address))

(defun fnb3-address-offset (address)
  (cdr address))

(defun fnb3-shift (address amount)
  (cons
   (fnb3-address-base address)
   (+ (fnb3-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t and byte memory t_1, together with the fixed source region
;; function, linked predicate specialized to t, and l_size constant.

(defstub fnb3-allocation (index) t)
(defstub fnb3-byte-memory (address) t)
(defstub fnb3-region (base) t)
(defstub fnb3-linked-op () t)
(defstub fnb3-l-size () t)
(defstub fnb3-l-cpu-smt-mask (index) t)
(defstub fnb3-l-idle-cpu (index) t)
(defstub fnb3-mask-memory-apply (memory-symbol address) t)
(defstub fnb3-mask-pointer-apply (pointer-symbol address) t)

(defun-sk fnb3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (fnb3-address-p address)
      (integerp (fnb3-byte-memory address)))
     (implies
      (integerp index)
      (integerp (fnb3-allocation index)))
     (implies
      (integerp base)
      (integerp (fnb3-region base))))))

(defun fnb3-linked-p ()
  (if (fnb3-linked-op) t nil))

(defun fnb3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun fnb3-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk fnb3-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (fnb3-address-p address)
      (and
       (integerp
        (fnb3-mask-memory-apply
         memory-symbol address))
       (fnb3-address-p
        (fnb3-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (fnb3-is-uint8-p
        (fnb3-l-idle-cpu index))
       (fnb3-address-p
        (fnb3-l-cpu-smt-mask index)))))))

(defun-sk fnb3-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (fnb3-address-p address)
     (equal
      (fnb3-mask-memory-apply
       'fnb3-zero-memory address)
      0))))

(defun-sk fnb3-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (fnb3-l-size)))
     (not
      (equal
       (fnb3-mask-memory-apply
        memory-symbol
        (fnb3-shift
         (fnb3-mask-pointer-apply
          pointer-symbol
          (fnb3-shift
           (fnb3-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk fnb3-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (fnb3-mask-memory-apply
         memory-symbol
         (fnb3-shift
          (fnb3-mask-pointer-apply
           pointer-symbol
           (fnb3-shift
            (fnb3-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (fnb3-l-size))
      (<= 0 j)
      (< j (fnb3-l-size)))
     (not
      (equal
       (fnb3-mask-memory-apply
        memory-symbol
        (fnb3-shift
         (fnb3-mask-pointer-apply
          pointer-symbol
          (fnb3-shift
           (fnb3-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk fnb3-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (fnb3-mask-memory-apply
         memory-symbol
         (fnb3-shift
          (fnb3-mask-pointer-apply
           pointer-symbol
           (fnb3-shift
            (fnb3-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (fnb3-mask-memory-apply
         memory-symbol
         (fnb3-shift
          (fnb3-mask-pointer-apply
           pointer-symbol
           (fnb3-shift
            (fnb3-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (fnb3-l-size))
      (<= 0 j)
      (< j (fnb3-l-size))
      (<= 0 k)
      (< k (fnb3-l-size)))
     (not
      (equal
       (fnb3-mask-memory-apply
        memory-symbol
        (fnb3-shift
         (fnb3-mask-pointer-apply
          pointer-symbol
          (fnb3-shift
           (fnb3-l-cpu-smt-mask i)
           0))
         k))
       0)))))


;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun fnb3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fnb3-address-base address)))
    (<= 0 (fnb3-address-offset address))
    (<=
     (+ (fnb3-address-offset address) length)
     (fnb3-allocation (fnb3-address-base address))))))

;; Preserve the source universal condition over every mathematical integer
;; index from i_1 (inclusive) to i_2 (exclusive).

(defun-sk fnb3-zero-prefix-p (a i1 i2)
  (forall (i3)
    (implies
     (integerp i3)
     (implies
      (<= i1 i3)
      (implies
       (< i3 i2)
       (equal
        (fnb3-byte-memory (fnb3-shift a i3))
        0))))))

(defun-sk
    ntp4vc-find-next-bit-0-assert-rte-mem-access-goal3-statement ()
  (forall
   (a i2 i i1)
   (implies
    (and
     (fnb3-function-types-p)
     (fnb3-scheduler-schema-types-p)
     (fnb3-zero-mask-memory-instance-p)
     (fnb3-q-mask-refl-p)
     (fnb3-q-mask-symm-p)
     (fnb3-q-mask-trans-p)
     (integerp (fnb3-l-size))
     (< 0 (fnb3-l-size))
     (<= (fnb3-l-size) 2147483647)
     (fnb3-address-p a)
     (integerp i2)
     (integerp i)
     (integerp i1))
    (let ((a1 (fnb3-shift a i2)))
      (implies
       (and
        (< i2 i)
        (<= i1 i2)
        (<= i (fnb3-l-size))
        (<= (fnb3-region (fnb3-address-base a)) 0)
        (fnb3-linked-p)
        (fnb3-is-uint32-p i)
        (fnb3-is-uint32-p i1)
        (fnb3-is-uint32-p i2)
        (fnb3-is-uint8-p (fnb3-byte-memory a1))
        (fnb3-valid-rd-p (fnb3-shift a 0) i)
        (fnb3-zero-prefix-p a i1 i2))
       (fnb3-valid-rd-p a1 1))))))

(value-triple :itpeval-statement-checked)

:q
