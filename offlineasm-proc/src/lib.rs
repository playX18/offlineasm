use offlineasm_ast::stmt::Toplevel;
use proc_macro::TokenStream;
#[proc_macro]
pub fn offlineasm(input: TokenStream) -> TokenStream {
    let toplevel = syn::parse::<Toplevel>(input);
    match toplevel {
        Ok(top) => {
            let seq = offlineasm_ast::transforms::prepass(&top).unwrap();
            println!("{}", seq);

            TokenStream::new()
        }
        Err(e) => e.to_compile_error().into(),
    }
}
