use proc_macro::{TokenStream,TokenTree,Delimiter};

fn skip_comma<T: Iterator<Item=TokenTree>>(ts: &mut T) {
    match ts.next() {
        | Some (TokenTree::Punct(p)) => assert_eq!(p.as_char(), ','),
        | _ => panic!("Expected comma")
    }
}

fn accept_token<T: Iterator<Item=TokenTree>>(ts: &mut T) -> TokenTree {
    match ts.next() {
        | Some(t) => t,
        | _ => panic!("early end")
    }
}

fn brace(ts: TokenStream) -> TokenTree {
    TokenTree::Group(proc_macro::Group::new(Delimiter::Brace, ts))
}

#[proc_macro]
pub fn unroll_for(ts: TokenStream) -> TokenStream {
    let mut i = ts.into_iter();
    let n_loops = accept_token(&mut i).to_string().parse::<u32>().unwrap();
    skip_comma(&mut i);
    let var = accept_token(&mut i).to_string();
    let var = &var[1..var.len()-1];
    skip_comma(&mut i);
    let start = accept_token(&mut i).to_string();
    skip_comma(&mut i);
    let increment = accept_token(&mut i).to_string();
    skip_comma(&mut i);
    let grouped_body = brace(TokenStream::from_iter(i));
    let chunks =
        (0..n_loops).map(|i| {
            let chunks = [
                format!("const {}: u32 = {} + {} * {};", var, start, i, increment).parse().unwrap(),
                TokenStream::from(grouped_body.clone()),
                ";".parse().unwrap()
            ];
            TokenStream::from(brace(TokenStream::from_iter(chunks)))
        })
    ;
    TokenStream::from(brace(TokenStream::from_iter(chunks.into_iter().flatten())))
    // "{ let i = 0; println!(\"FROM MACRO{}\", i); }".parse().unwrap()
}
