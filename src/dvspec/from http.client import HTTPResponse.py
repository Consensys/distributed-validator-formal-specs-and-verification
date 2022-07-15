from http.client import HTTPResponse
import string


async def get_request(url: string) -> HTTPResponse

async def foo():
    response1 = get_request("http://..../fork")
    response2 = get_request("http://..../attestation_data")