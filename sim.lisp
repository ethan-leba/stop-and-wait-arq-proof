; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro let-match* (binds body)
  (case-match binds
    ('() body)
    (((pat val) . rst)
     `(let ((greatbadness ,val))
	(case-match greatbadness
	  (,pat (let-match* ,rst ,body)))))))

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state `(sendstate ,data ,nat))

(defdata receiver-state `(recvstate ,data ,nat))

(defdata ack nat)

(defdata packet `(packet ,atom ,ack))

(defdata event-deck (listof nil))
;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state `(sim-state ,sender-state ,receiver-state))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out `(sender-out ,sender-state ,packet))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata receiver-out `(receiver-out ,receiver-state ,ack))

(defdata result (oneof data 'error))

;; ---- Functions ----

(definec seq-num-okp (sender-state :sender-state) :bool
  (let-match* ((('sendstate data seq-num) sender-state))
    (> (len data) seq-num)))

(set-ignore-ok t)
(definec simulator-state-check (sim :sim-state) :bool
  (let-match* ((('sim-state sender-state &) sim))
    (seq-num-okp sender-state)))

(definec simulator-step (sim :sim-state) :sim-state
  :function-contract-strictp nil
  (if (simulator-state-check sim)
      (let-match* ((('sim-state ('sendstate sdata sseq) ('recvstate rdata rseq)) sim))
	`(sim-state (sendstate ,sdata ,(1+ sseq))
		    (recvstate ,(app rdata (list (nth (len rdata) sdata))) ,rseq)))
    sim))

(check= (simulator-step '(sim-state (sendstate (1 2) 0) (recvstate nil 0)))
	'(sim-state (sendstate (1 2) 1) (recvstate (1) 0) (nil nil)))

(check= (simulator-step '(sim-state (sendstate (1) 0) (recvstate (4 5 6) 0)))
	'(sim-state (sendstate (1) 1) (recvstate (4 5 6 1) 0) ()))


(definec simulator-state-check2 (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate data seqnum) &) sim))
    (>= (len data) seqnum)))

(definec simulator (sim :sim-state steps :event-deck) :sim-state
  :function-contract-strictp nil
  :body-contracts-strictp nil
  :skip-tests t
  :ic (simulator-state-check2 sim)
  (let-match* ((('sim-state ('sendstate ss sseq) ('recvstate rs rseq)) sim))
    (cond
     ((or (equal sseq (len ss)) (lendp steps)) sim)
     (T (simulator-step (simulator sim (cdr steps)))))))

(check= (simulator '(sim-state (sendstate (1 2 3) 0) (recvstate (4 5 6) 0)) '(nil nil nil))
	'(4 5 6 1 2 3))

(definec simulator* (data :data steps :event-deck) :data
  :function-contract-strictp nil
  :ic (>= (len data) (len steps))
  (let-match* ((('sim-state & ('recvstate rs &))
		(simulator `(sim-state (sendstate ,data 0) (recvstate nil 0)) steps)))
    rs))

(check= (simulator* '(4 5 6) '(nil nil nil))
	'(4 5 6))

;; ---- Proofs ----

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

;; First confirm test? works
(test? (implies (and (datap d)
		     (event-deckp n)
		     (>= (len d) (len n)))
		(prefixp (simulator* d n) d)))

(defthm prefix-nth
  (implies (and
	    (tlp x)
	    (tlp y)
	    (prefixp x y)
	    (< (len x) (len y)))
	   (prefixp (app x (list (nth (len x) y))) y)))

(definec rs-prefix-of-ssp (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate ss &) ('recvstate rs &)) sim))
    (prefixp rs ss)))

(definec seqnum-consistent (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate & sseq) ('recvstate rs rseq)) sim))
    (== (len rs) rseq)))

#| == The proof sketch ==

We know receiver state is a prefix of sender state (via C3), and that
the sender sequence number is equal to it's length (via C4). So we should
be able to utilize the prefix-nth lemma to show that the prefix property holds.
|#

(defthm simulator-step-prefix-property
  (test? (implies (and (sim-statep sim)
		 ;; (simulator-state-check2 sim)
		 (rs-prefix-of-ssp sim)
		 ;; (seqnum-consistent sim)
		 )
		  (rs-prefix-of-ssp (simulator-step sim))))
  :hints (("Goal" :do-not-induct t
	   :do-not generalize)
	  ("Subgoal 2'5'" :use (:instance prefix-nth (y sim8) (x sim9)))))

(in-theory (disable simulator-step-definition-rule))
(defthm simulator-prefix-property
  (implies (and (sim-statep sim)
		(event-deckp evt)
		(simulator-state-check2 sim)
		(rs-prefix-of-ssp sim)
		(seqnum-consistent sim))
	   (rs-prefix-of-ssp (simulator sim evt)))
  :hints (("Goal" :induct (simulator sim evt))
	  ("Subgoal *1/2" :use (:instance simulator-definition-rule))
	  ("Subgoal *1/2.87" :use (:instance simulator-step-prefix-property (sim (SIMULATOR SIM (CDR EVT)))))))
