(function() {var implementors = {
"fcomm":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://docs.rs/anyhow/1.0.75/anyhow/struct.Error.html\" title=\"struct anyhow::Error\">Error</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"https://docs.rs/hex/0.4.3/hex/error/enum.FromHexError.html\" title=\"enum hex::error::FromHexError\">FromHexError</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/store/struct.Error.html\" title=\"struct lurk::store::Error\">Error</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;SynthesisError&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/public_parameters/error/enum.Error.html\" title=\"enum lurk::public_parameters::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/z_data/serde/enum.SerdeError.html\" title=\"enum lurk::z_data::serde::SerdeError\">SerdeError</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"fcomm/error/enum.Error.html\" title=\"enum fcomm::error::Error\">Error</a>"]],
"lurk":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/error/enum.ReductionError.html\" title=\"enum lurk::error::ReductionError\">ReductionError</a>&gt; for <a class=\"enum\" href=\"lurk/error/enum.ProofError.html\" title=\"enum lurk::error::ProofError\">ProofError</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/coprocessor/trie/struct.LookupCoprocessor.html\" title=\"struct lurk::coprocessor::trie::LookupCoprocessor\">LookupCoprocessor</a>&lt;F&gt;&gt; for <a class=\"enum\" href=\"lurk/coprocessor/trie/enum.TrieCoproc.html\" title=\"enum lurk::coprocessor::trie::TrieCoproc\">TrieCoproc</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"lurk/public_parameters/error/enum.Error.html\" title=\"enum lurk::public_parameters::error::Error\">Error</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/eval/lang/struct.DummyCoprocessor.html\" title=\"struct lurk::eval::lang::DummyCoprocessor\">DummyCoprocessor</a>&lt;F&gt;&gt; for <a class=\"enum\" href=\"lurk/eval/lang/enum.Coproc.html\" title=\"enum lurk::eval::lang::Coproc\">Coproc</a>&lt;F&gt;"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>, C: <a class=\"trait\" href=\"lurk/coprocessor/trait.Coprocessor.html\" title=\"trait lurk::coprocessor::Coprocessor\">Coprocessor</a>&lt;F&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;<a class=\"struct\" href=\"lurk/eval/lang/struct.Lang.html\" title=\"struct lurk::eval::lang::Lang\">Lang</a>&lt;F, C&gt;&gt; for <a class=\"struct\" href=\"lurk/lem/struct.Func.html\" title=\"struct lurk::lem::Func\">Func</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.Op2.html\" title=\"enum lurk::tag::Op2\">Op2</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>"],["impl&lt;Name: <a class=\"trait\" href=\"lurk/hash_witness/trait.HashName.html\" title=\"trait lurk::hash_witness::HashName\">HashName</a>, T: <a class=\"trait\" href=\"lurk/hash_witness/trait.ContentAddressed.html\" title=\"trait lurk::hash_witness::ContentAddressed\">ContentAddressed</a>&lt;F&gt;, const L: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>, F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/hash_witness/struct.HashWitness.html\" title=\"struct lurk::hash_witness::HashWitness\">HashWitness</a>&lt;Name, T, L, F&gt;&gt; for <a class=\"struct\" href=\"lurk/hash_witness/struct.CircuitHashWitness.html\" title=\"struct lurk::hash_witness::CircuitHashWitness\">CircuitHashWitness</a>&lt;Name, T, L, F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.ExprTag.html\" title=\"enum lurk::tag::ExprTag\">ExprTag</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/uint/enum.UInt.html\" title=\"enum lurk::uint::UInt\">UInt</a>&gt; for <a class=\"enum\" href=\"lurk/enum.Num.html\" title=\"enum lurk::Num\">Num</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/store/struct.Error.html\" title=\"struct lurk::store::Error\">Error</a>&gt; for <a class=\"enum\" href=\"lurk/error/enum.ReductionError.html\" title=\"enum lurk::error::ReductionError\">ReductionError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>&gt; for <a class=\"enum\" href=\"lurk/uint/enum.UInt.html\" title=\"enum lurk::uint::UInt\">UInt</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/coprocessor/trie/struct.InsertCoprocessor.html\" title=\"struct lurk::coprocessor::trie::InsertCoprocessor\">InsertCoprocessor</a>&lt;F&gt;&gt; for <a class=\"enum\" href=\"lurk/coprocessor/trie/enum.TrieCoproc.html\" title=\"enum lurk::coprocessor::trie::TrieCoproc\">TrieCoproc</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.ContTag.html\" title=\"enum lurk::tag::ContTag\">ContTag</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.Op1.html\" title=\"enum lurk::tag::Op1\">Op1</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://docs.rs/serde_json/1.0.107/serde_json/error/struct.Error.html\" title=\"struct serde_json::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"lurk/public_parameters/error/enum.Error.html\" title=\"enum lurk::public_parameters::error::Error\">Error</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>&gt; for <a class=\"enum\" href=\"lurk/enum.Num.html\" title=\"enum lurk::Num\">Num</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;SynthesisError&gt; for <a class=\"enum\" href=\"lurk/error/enum.ProofError.html\" title=\"enum lurk::error::ProofError\">ProofError</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/ptr/struct.GPtr.html\" title=\"struct lurk::ptr::GPtr\">GPtr</a>&lt;F, <a class=\"enum\" href=\"lurk/tag/enum.ContTag.html\" title=\"enum lurk::tag::ContTag\">ContTag</a>&gt;&gt; for <a class=\"enum\" href=\"lurk/eval/enum.Status.html\" title=\"enum lurk::eval::Status\">Status</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/lem/enum.Tag.html\" title=\"enum lurk::lem::Tag\">Tag</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.char.html\">char</a>&gt; for <a class=\"type\" href=\"lurk/ptr/type.Ptr.html\" title=\"type lurk::ptr::Ptr\">Ptr</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.Op1.html\" title=\"enum lurk::tag::Op1\">Op1</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"lurk/symbol/struct.Symbol.html\" title=\"struct lurk::symbol::Symbol\">Symbol</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/uint/enum.UInt.html\" title=\"enum lurk::uint::UInt\">UInt</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/coprocessor/trie/struct.NewCoprocessor.html\" title=\"struct lurk::coprocessor::trie::NewCoprocessor\">NewCoprocessor</a>&lt;F&gt;&gt; for <a class=\"enum\" href=\"lurk/coprocessor/trie/enum.TrieCoproc.html\" title=\"enum lurk::coprocessor::trie::TrieCoproc\">TrieCoproc</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;NovaError&gt; for <a class=\"enum\" href=\"lurk/error/enum.ProofError.html\" title=\"enum lurk::error::ProofError\">ProofError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt; for <a class=\"enum\" href=\"lurk/hash/enum.HashArity.html\" title=\"enum lurk::hash::HashArity\">HashArity</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.ContTag.html\" title=\"enum lurk::tag::ContTag\">ContTag</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>"],["impl&lt;F: <a class=\"trait\" href=\"lurk/field/trait.LurkField.html\" title=\"trait lurk::field::LurkField\">LurkField</a>, C: <a class=\"trait\" href=\"lurk/coprocessor/trait.Coprocessor.html\" title=\"trait lurk::coprocessor::Coprocessor\">Coprocessor</a>&lt;F&gt;, S: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;<a class=\"struct\" href=\"lurk/symbol/struct.Symbol.html\" title=\"struct lurk::symbol::Symbol\">Symbol</a>&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.tuple.html\">(S, C)</a>&gt; for <a class=\"struct\" href=\"lurk/eval/lang/struct.Binding.html\" title=\"struct lurk::eval::lang::Binding\">Binding</a>&lt;F, C&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.Op2.html\" title=\"enum lurk::tag::Op2\">Op2</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"lurk/store/struct.Error.html\" title=\"struct lurk::store::Error\">Error</a>&gt; for <a class=\"enum\" href=\"lurk/error/enum.ProofError.html\" title=\"enum lurk::error::ProofError\">ProofError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"lurk/tag/enum.ExprTag.html\" title=\"enum lurk::tag::ExprTag\">ExprTag</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()